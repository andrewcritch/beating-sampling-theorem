import BstLean.Part142Anchor
import BstLean.Part142Spread
import BstLean.Part142FD

/-!
# Part 142, item 2 (`kernel142`): the `L²` bound of the DISTANCE kernel, assembly

Role: `delegations/statements/p142-spec.md`, item 2. The distance kernel is
`D = (k(x, x) + k(x′, x′))/2 − k(x, x′) = (2/m_F)·|H_A(x) − H_A(x′)|²/2` (`kernD`; `kD` of
`Part142Spread` at `x = x(u)`, `x′ = x(u′)`). Its reference value is `S·(1 − κ^{∘6}(0))`,
`S = 4/n`.

* `kernD_fixed_of`: for fixed unit `x, x′`, over `(A, A′, F)`, from the link of `F`
  (`F_dist_L2_of`) and the links of `A` (`Part142AgentD`):
  `‖D − S·(1 − κ^{∘4}(⟨x, x′⟩))‖₂ ≤ S·(2φ₁δ₁ + 2φ₂(1 + 5/m_A)√(1 + 2/n) + 2φ₃√eps4 + φ₄δ₂ + α)`.
* `kernDist_L2_of`: over `(u, u′) ⊗ (W, A, A′, F)`, from a bound
  `S·(g₀ + g₁(1 − κ(κ(t))) + g₂(1 − t))` at fixed inputs (`t = ⟨x, x′⟩`) and
  `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ τ`:
  `‖kD − S(1 − κ^{∘6}(0))‖₂ ≤ S·(g₀ + g₁(1 − κ^{∘4}(0) + τ) + g₂(1 − κ(κ(0)) + τ) + σ₄τ)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139

section General

variable {N mW n mA mF : ℕ}

/-- **The distance kernel at fixed inputs**: `(k(x, x) + k(x′, x′))/2 − k(x, x′)`, the same
Agent network at both inputs. -/
noncomputable def kernD (F : MlpParam n mF 1) (A : MlpParam n mA n) (x x' : Fin n → ℝ) : ℝ :=
  (kern F A A x x + kern F A A x' x') / 2 - kern F A A x x'

lemma kD_eq_kernD (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) :
    kD ω = kernD ω.2.2.2.2 ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2) := rfl

lemma measurable_kernD_p (x x' : Fin n → ℝ) :
    Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kernD p.2.2 p.1 x x') := by
  unfold kernD
  have h : ∀ a b : Fin n → ℝ, Measurable (fun p : MlpParam n mA n × MlpParam n mA n ×
      MlpParam n mF 1 => kern p.2.2 p.1 p.1 a b) := fun a b =>
    measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst measurable_fst
      measurable_const measurable_const
  exact (((h x x).add (h x' x')).div_const 2).sub (h x x')

lemma measurable_phiD_mlp {G : ℝ → ℝ} (hG : Continuous G) {k m q : ℕ} (z z' : Fin k → ℝ) :
    Measurable (fun θ : MlpParam k m q => phiD G (mlpEval θ z) (mlpEval θ z')) := by
  unfold phiD
  exact (((measurable_normSq.comp (measurable_mlpEval_param z)).add
    (measurable_normSq.comp (measurable_mlpEval_param z'))).div_const 2).sub
    (measurable_psi_mlp hG z z')

/-- `‖|A(x)|²‖₂ = 2(1 + 5/m_A)√(1 + 2/n)` for a unit `x`. -/
lemma agent_normSq_L2 (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x : Fin n → ℝ} (hx : normSq x = 1) :
    L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => normSq (mlpEval A x))
      (2 * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (mlp_nrm_pair_L2 (q := n) hmA hx hx).congr_fun (fun A => nrm_mul_self _)
  refine h.congr_bound ?_
  field_simp

/-- `‖|A(x)|² − 2‖₂ = 2√eps4` for a unit `x`. -/
lemma agent_normSq_dev_L2 (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x : Fin n → ℝ} (hx : normSq x = 1) :
    L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => normSq (mlpEval A x) - 2)
      (2 * √(eps4 n mA)) := by
  obtain ⟨iv, ev⟩ := agent_sq_var hn hmA hx
  have hmeas : Measurable (fun A : MlpParam n mA n => normSq (mlpEval A x) - 2) :=
    (measurable_normSq.comp (measurable_mlpEval_param x)).sub measurable_const
  refine L2le.mk' hmeas.aestronglyMeasurable iv ?_
  rw [ev, mul_pow, Real.sq_sqrt (eps4_nonneg n mA)]
  norm_num

/-- **The distance kernel at fixed unit inputs, over `(A, A′, F)`**, from the link of `F` and
the three facts of the Agent network. -/
theorem kernD_fixed_of (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {φ1 φ2 φ3 φ4 α δ1 δ2 : ℝ}
    (h1 : 0 ≤ φ1) (h2 : 0 ≤ φ2) (h3 : 0 ≤ φ3) (h4 : 0 ≤ φ4) (hα : 0 ≤ α) (hδ1 : 0 ≤ δ1)
    (hδ2 : 0 ≤ δ2)
    (hF : ∀ y y' : Fin n → ℝ, L2le (mlpGauss n mF 1)
      (fun F : MlpParam n mF 1 =>
        2 / (mF : ℝ) * eD (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
          2 / (n : ℝ) * phiD (kappa ∘ kappa) y y')
      (2 / (n : ℝ) * (φ1 * normSq (y - y') + φ2 * (normSq y + normSq y') +
        φ3 * |normSq y - normSq y'| + φ4 * dlt y y')))
    (hA : L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x'))) (2 * α))
    (hDiff : L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x')) (4 * δ1))
    (hDlt : L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => dlt (mlpEval A x) (mlpEval A x')) (2 * δ2)) :
    L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kernD p.2.2 p.1 x x' - 4 / (n : ℝ) * (1 - kappa^[4] (dotp x x')))
      (4 / (n : ℝ) * (2 * φ1 * δ1 + 2 * φ2 * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))) +
        2 * φ3 * √(eps4 n mA) + φ4 * δ2 + α)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  have hGc : Continuous (kappa ∘ kappa) := continuous_kappa.comp continuous_kappa
  have he4 := Real.sqrt_nonneg (eps4 n mA)
  set N0 : ℝ := (1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ)) with hN0
  have hN00 : 0 ≤ N0 := by rw [hN0]; positivity
  -- the bound of the link of `F`, in `L²` over `A`
  have nS := agent_normSq_L2 hn hmA hx
  have nS' := agent_normSq_L2 hn hmA hx'
  have dS := agent_normSq_dev_L2 hn hmA hx
  have dS' := agent_normSq_dev_L2 hn hmA hx'
  have sSum := nS.add0 nS' (by positivity) (by positivity)
  have sDif : L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => |normSq (mlpEval A x) - normSq (mlpEval A x')|)
      (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) := by
    have h0 := dS.add0 dS'.neg (by positivity) (by positivity)
    exact L2le.abs' (h0.congr_fun fun A => by ring)
  have hg : L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => 2 / (n : ℝ) * (φ1 * normSq (mlpEval A x - mlpEval A x') +
        φ2 * (normSq (mlpEval A x) + normSq (mlpEval A x')) +
        φ3 * |normSq (mlpEval A x) - normSq (mlpEval A x')| +
        φ4 * dlt (mlpEval A x) (mlpEval A x')))
      (2 / (n : ℝ) * (φ1 * (4 * δ1) + φ2 * (2 * N0 + 2 * N0) +
        φ3 * (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) + φ4 * (2 * δ2))) := by
    have a1 := hDiff.const_mul_nonneg h1
    have a2 := sSum.const_mul_nonneg h2
    have a3 := sDif.const_mul_nonneg h3
    have a4 := hDlt.const_mul_nonneg h4
    have s12 := a1.add0 a2 (by positivity) (by positivity)
    have s123 := s12.add0 a3 (by positivity) (by positivity)
    have s1234 := s123.add0 a4 (by positivity) (by positivity)
    exact s1234.const_mul_nonneg (by positivity)
  have m1 := measurable_kernD_p (mA := mA) (mF := mF) x x'
  have m2 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      phiD (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x')) :=
    (measurable_phiD_mlp hGc x x').comp measurable_fst
  have b1 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kernD p.2.2 p.1 x x' -
          2 / (n : ℝ) * phiD (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x'))
      (2 / (n : ℝ) * (φ1 * (4 * δ1) + φ2 * (2 * N0 + 2 * N0) +
        φ3 * (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) + φ4 * (2 * δ2))) := by
    refine L2le.prod' (m1.sub (m2.const_mul _)).aestronglyMeasurable hg
      (Filter.Eventually.of_forall fun A => ?_)
    refine ((hF (mlpEval A x) (mlpEval A x')).comp_snd).congr_fun fun y => ?_
    change _ = kernD y.2 A x x' - _
    unfold kernD
    rw [kernD_eq]
  have b2 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        2 / (n : ℝ) * (phiD (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x') -
          2 * (1 - kappa^[4] (dotp x x'))))
      (2 / (n : ℝ) * (2 * α)) :=
    (hA.const_mul_nonneg (c := 2 / (n : ℝ)) (by positivity)).comp_fst
      (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))
  have h12 := b1.add0 b2 (by positivity) (by positivity)
  refine (h12.congr_fun fun p => ?_).congr_bound ?_
  · field_simp
    ring
  · field_simp
    ring

/-- `κ∘κ` is 1-Lipschitz on `[−1, 1]`. -/
lemma kk_lip {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |kappa (kappa s) - kappa (kappa t)| ≤ |s - t| := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  rcases le_total t s with h | h
  · have h1 := hG.lip ht.1 h hs.2
    have h2 := hG.mono ht hs h
    simp only [Function.comp_apply] at h1 h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h1
  · have h1 := hG.lip hs.1 h ht.2
    have h2 := hG.mono hs ht h
    simp only [Function.comp_apply] at h1 h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂` on `(u, u′) ⊗ W`, from the bound on the whole space. -/
lemma tX_L2_marg (hN : 1 ≤ N) {τ : ℝ}
    (hT : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1) - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ := by
  have := lawU2_prob hN
  have hφ : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      (ω.1, ω.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hmap : ((lawU2 N).prod (lawR N mW n mA mF)).map
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => (ω.1, ω.2.1)) =
      (lawU2 N).prod (mlpGauss N mW n) := by
    have h1 : (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => (ω.1, ω.2.1)) =
        Prod.map id Prod.fst := by
      funext ω; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id]
    unfold lawR
    rw [Measure.map_fst_prod]
    simp
  have hf : AEStronglyMeasurable
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0))
      (((lawU2 N).prod (lawR N mW n mA mF)).map
        (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => (ω.1, ω.2.1))) :=
    (measurable_tX.sub measurable_const).aestronglyMeasurable
  have h := L2le.of_comp_map hφ hf hT
  rwa [hmap] at h

/-- **The distance kernel under `(u, u′) ⊗ (W, A, A′, F)`.** -/
theorem kernDist_L2_of (hn : 1 ≤ n) (hN : 1 ≤ N) {g0 g1 g2 τ : ℝ} (h0 : 0 ≤ g0)
    (h1 : 0 ≤ g1) (h2 : 0 ≤ g2) (hτ : 0 ≤ τ)
    (hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kernD p.2.2 p.1 x x' - 4 / (n : ℝ) * (1 - kappa^[4] (dotp x x')))
        (4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (dotp x x'))) + g2 * (1 - dotp x x'))))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * (g0 + g1 * (1 - kappa^[4] 0 + τ) + g2 * (1 - kappa (kappa 0) + τ) +
        sig4 * τ)) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs4 := sig4_nonneg
  set q := kappa (kappa 0) with hq
  have hqm : q ∈ Icc (-1 : ℝ) 1 := kk_memIcc KGood.zero_mem
  have hq1 : q ≤ 1 := hqm.2
  have e40 : kappa^[4] 0 = kappa (kappa q) := rfl
  have h40 : kappa^[4] 0 ≤ 1 := by
    rw [e40]; exact (kk_memIcc hqm).2
  set μ1 := (lawU2 N).prod (mlpGauss N mW n) with hμ1
  set P := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hP
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have mtX : Measurable (tX (N := N) (mW := mW) (n := n)) := measurable_tX
  -- the function on `μ1 ⊗ P`
  have mK : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
      (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
      kernD z.2.2.2 z.2.1 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2)) := by
    have hk : ∀ (fx fx' : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
        (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) → (Fin n → ℝ)),
        Measurable fx → Measurable fx' →
        Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
          kern z.2.2.2 z.2.1 z.2.1 (fx z) (fx' z)) := fun fx fx' hfx hfx' =>
      measurable_kern_comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
        (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_snd) hfx hfx'
    have mx : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
        (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) => xW z.1.2 z.1.1.1) :=
      measurable_xW_comp (measurable_snd.comp measurable_fst)
        (measurable_fst.comp (measurable_fst.comp measurable_fst))
    have mx' : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
        (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) => xW z.1.2 z.1.1.2) :=
      measurable_xW_comp (measurable_snd.comp measurable_fst)
        (measurable_snd.comp (measurable_fst.comp measurable_fst))
    unfold kernD
    exact (((hk _ _ mx mx).add (hk _ _ mx' mx')).div_const 2).sub (hk _ _ mx mx')
  have mT1 : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
      (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) => tX z.1) :=
    mtX.comp measurable_fst
  -- the bound at fixed inputs, in `L²(μ1)`
  set C0 : ℝ := g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - q) with hC0
  have hC00 : 0 ≤ C0 := by
    rw [hC0]
    have : 0 ≤ g1 * (1 - kappa^[4] 0) := mul_nonneg h1 (by linarith)
    have : 0 ≤ g2 * (1 - q) := mul_nonneg h2 (by linarith)
    linarith
  have hg : L2le μ1
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z)))
      (4 / (n : ℝ) * (C0 + (g1 + g2) * τ)) := by
    have c1 : L2le μ1 (fun _ : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => C0) C0 := by
      have := L2le.const (μ := μ1) C0
      rwa [abs_of_nonneg hC00] at this
    have c2 := (L2le.abs' hT).const_mul_nonneg (c := g1 + g2) (by linarith)
    have c3 := (c1.add0 c2 hC00 (by positivity)).const_mul_nonneg (c := 4 / (n : ℝ))
      (by positivity)
    have mm : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z))) :=
      ((measurable_const.add ((measurable_const.sub (hkk.comp mtX)).const_mul _)).add
        ((measurable_const.sub mtX).const_mul _)).const_mul _
    refine L2le.of_abs_le mm.aestronglyMeasurable c3 (fun z => ?_)
    have ht := tX_mem (N := N) (mW := mW) hn z
    have hkt := kk_memIcc ht
    have hl := kk_lip ht hqm
    rw [← e40] at hl
    have hl' := abs_le.mp hl
    have habs := abs_nonneg (tX z - q)
    have hle := le_abs_self (tX z - q)
    have hge := neg_abs_le (tX z - q)
    have u1 : 0 ≤ 1 - kappa (kappa (tX z)) := by linarith [hkt.2]
    have u2 : 1 - kappa (kappa (tX z)) ≤ 1 - kappa^[4] 0 + |tX z - q| := by linarith
    have u3 : 0 ≤ 1 - tX z := by linarith [ht.2]
    have u4 : 1 - tX z ≤ 1 - q + |tX z - q| := by linarith
    have inner0 : 0 ≤ g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) := by positivity
    have innerle : g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) ≤
        C0 + (g1 + g2) * |tX z - q| := by
      have a1 := mul_le_mul_of_nonneg_left u2 h1
      have a2 := mul_le_mul_of_nonneg_left u4 h2
      rw [hC0]
      nlinarith
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left innerle (by positivity)
  -- link 1
  have B1 : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        kernD z.2.2.2 z.2.1 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2) -
          4 / (n : ℝ) * (1 - kappa^[4] (tX z.1)))
      (4 / (n : ℝ) * (C0 + (g1 + g2) * τ)) := by
    refine L2le.prod' (mK.sub ((measurable_const.sub (hk4.comp mT1)).const_mul _)).aestronglyMeasurable
      hg (Filter.Eventually.of_forall fun z => ?_)
    exact hS (xW z.2 z.1.1) (xW z.2 z.1.2) (normSq_xW hn _ _) (normSq_xW hn _ _)
  -- link 2
  have B2 : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (tX z.1)))
      (4 / (n : ℝ) * (sig4 * τ)) := by
    have h0 : L2le μ1 (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (tX z))) (4 / (n : ℝ) * (sig4 * τ)) := by
      have c0 := (hT.const_mul_nonneg hs4).const_mul_nonneg (c := 4 / (n : ℝ)) (by positivity)
      refine L2le.of_abs_le
        ((measurable_const.sub (hk4.comp mtX)).const_mul _).aestronglyMeasurable c0 (fun z => ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs4, abs_sub_comm]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact iter4_chord (tX_mem hn z)
    exact h0.comp_fst
  have B12 := B1.add0 B2 (by positivity) (by positivity)
  -- transfer to `(u, u′) ⊗ (W, (A, A′, F))`
  have hmap : (μ1.prod P).map MeasurableEquiv.prodAssoc = (lawU2 N).prod (lawR N mW n mA mF) := by
    rw [hμ1, hP, Measure.prodAssoc_prod]
    rfl
  have hf : AEStronglyMeasurable
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      ((μ1.prod P).map MeasurableEquiv.prodAssoc) :=
    (measurable_kD.sub measurable_const).aestronglyMeasurable
  have key : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
          kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (MeasurableEquiv.prodAssoc z))
      (4 / (n : ℝ) * (g0 + g1 * (1 - kappa^[4] 0 + τ) + g2 * (1 - q + τ) + sig4 * τ)) := by
    refine (B12.congr_fun fun z => ?_).congr_bound ?_
    · change _ = kernD z.2.2.2 z.2.1 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2) - _
      ring
    · rw [hC0]; ring
  have h := L2le.of_comp_map (MeasurableEquiv.measurable _) hf key
  rwa [hmap] at h

/-- **The distance kernel under `(u, u′) ⊗ (W, A, A′, F)`, general form**: the bound at fixed
inputs may have a term in `1 − κ^{∘4}(t)` and a coefficient `g₁` of any sign. -/
theorem kernDist_L2_gen (hn : 1 ≤ n) (hN : 1 ≤ N) {g0 g1 g2 g3 τ : ℝ}
    (h2 : 0 ≤ g2) (h3 : 0 ≤ g3) (hτ : 0 ≤ τ)
    (hC : 0 ≤ g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - kappa (kappa 0)) + g3 * (1 - kappa^[6] 0))
    (hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kernD p.2.2 p.1 x x' - 4 / (n : ℝ) * (1 - kappa^[4] (dotp x x')))
        (4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (dotp x x'))) + g2 * (1 - dotp x x') +
          g3 * (1 - kappa^[4] (dotp x x')))))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * (g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - kappa (kappa 0)) +
        g3 * (1 - kappa^[6] 0) + (|g1| + g2 + g3 * sig4) * τ + sig4 * τ)) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs4 := sig4_nonneg
  set q := kappa (kappa 0) with hq
  have hqm : q ∈ Icc (-1 : ℝ) 1 := kk_memIcc KGood.zero_mem
  have hq1 : q ≤ 1 := hqm.2
  have e40 : kappa^[4] 0 = kappa (kappa q) := rfl
  have h40 : kappa^[4] 0 ≤ 1 := by
    rw [e40]; exact (kk_memIcc hqm).2
  set μ1 := (lawU2 N).prod (mlpGauss N mW n) with hμ1
  set P := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hP
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have mtX : Measurable (tX (N := N) (mW := mW) (n := n)) := measurable_tX
  -- the function on `μ1 ⊗ P`
  have mK : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
      (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
      kernD z.2.2.2 z.2.1 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2)) := by
    have hk : ∀ (fx fx' : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
        (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) → (Fin n → ℝ)),
        Measurable fx → Measurable fx' →
        Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
          kern z.2.2.2 z.2.1 z.2.1 (fx z) (fx' z)) := fun fx fx' hfx hfx' =>
      measurable_kern_comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
        (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_snd) hfx hfx'
    have mx : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
        (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) => xW z.1.2 z.1.1.1) :=
      measurable_xW_comp (measurable_snd.comp measurable_fst)
        (measurable_fst.comp (measurable_fst.comp measurable_fst))
    have mx' : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
        (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) => xW z.1.2 z.1.1.2) :=
      measurable_xW_comp (measurable_snd.comp measurable_fst)
        (measurable_snd.comp (measurable_fst.comp measurable_fst))
    unfold kernD
    exact (((hk _ _ mx mx).add (hk _ _ mx' mx')).div_const 2).sub (hk _ _ mx mx')
  have mT1 : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
      (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) => tX z.1) :=
    mtX.comp measurable_fst
  -- the bound at fixed inputs, in `L²(μ1)`
  set C0 : ℝ := g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - q) + g3 * (1 - kappa^[6] 0) with hC0
  have hC00 : 0 ≤ C0 := hC
  set Lc : ℝ := |g1| + g2 + g3 * sig4 with hLc
  have hLc0 : 0 ≤ Lc := by rw [hLc]; positivity
  have hg : L2le μ1
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) +
          g3 * (1 - kappa^[4] (tX z))))
      (4 / (n : ℝ) * (C0 + Lc * τ)) := by
    have c1 : L2le μ1 (fun _ : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => C0) C0 := by
      have := L2le.const (μ := μ1) C0
      rwa [abs_of_nonneg hC00] at this
    have c2 := (L2le.abs' hT).const_mul_nonneg (c := Lc) hLc0
    have c3 := (c1.add0 c2 hC00 (by positivity)).const_mul_nonneg (c := 4 / (n : ℝ))
      (by positivity)
    have mm : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) +
          g3 * (1 - kappa^[4] (tX z)))) :=
      (((measurable_const.add ((measurable_const.sub (hkk.comp mtX)).const_mul _)).add
        ((measurable_const.sub mtX).const_mul _)).add
        ((measurable_const.sub (hk4.comp mtX)).const_mul _)).const_mul _
    refine L2le.of_abs_le mm.aestronglyMeasurable c3 (fun z => ?_)
    have ht := tX_mem (N := N) (mW := mW) hn z
    have hkt := kk_memIcc ht
    have hl := kk_lip ht hqm
    rw [← e40] at hl
    have hl' := abs_le.mp hl
    have habs := abs_nonneg (tX z - q)
    have hle := le_abs_self (tX z - q)
    have hge := neg_abs_le (tX z - q)
    have hch := iter4_chord ht
    have hch' := abs_le.mp hch
    have hs4a := mul_nonneg hs4 habs
    have u4 : 1 - tX z ≤ 1 - q + |tX z - q| := by linarith
    have t1 : g1 * (1 - kappa (kappa (tX z))) ≤ g1 * (1 - kappa^[4] 0) + |g1| * |tX z - q| := by
      have e : g1 * (1 - kappa (kappa (tX z))) =
          g1 * (1 - kappa^[4] 0) + g1 * (kappa^[4] 0 - kappa (kappa (tX z))) := by ring
      rw [e]
      have : g1 * (kappa^[4] 0 - kappa (kappa (tX z))) ≤ |g1| * |tX z - q| := by
        calc g1 * (kappa^[4] 0 - kappa (kappa (tX z)))
            ≤ |g1 * (kappa^[4] 0 - kappa (kappa (tX z)))| := le_abs_self _
          _ = |g1| * |kappa (kappa (tX z)) - kappa^[4] 0| := by rw [abs_mul, abs_sub_comm]
          _ ≤ |g1| * |tX z - q| := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      linarith
    have t1' : g1 * (1 - kappa^[4] 0) - |g1| * |tX z - q| ≤ g1 * (1 - kappa (kappa (tX z))) := by
      have e : g1 * (1 - kappa (kappa (tX z))) =
          g1 * (1 - kappa^[4] 0) + g1 * (kappa^[4] 0 - kappa (kappa (tX z))) := by ring
      rw [e]
      have : -(|g1| * |tX z - q|) ≤ g1 * (kappa^[4] 0 - kappa (kappa (tX z))) := by
        have h5 : |g1 * (kappa^[4] 0 - kappa (kappa (tX z)))| ≤ |g1| * |tX z - q| := by
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
        linarith [neg_abs_le (g1 * (kappa^[4] 0 - kappa (kappa (tX z))))]
      linarith
    have t2 : g2 * (1 - tX z) ≤ g2 * (1 - q) + g2 * |tX z - q| := by
      have := mul_le_mul_of_nonneg_left u4 h2
      linarith
    have t2' : g2 * (1 - q) - g2 * |tX z - q| ≤ g2 * (1 - tX z) := by
      have : 1 - q - |tX z - q| ≤ 1 - tX z := by linarith
      have := mul_le_mul_of_nonneg_left this h2
      linarith
    have t3 : g3 * (1 - kappa^[4] (tX z)) ≤ g3 * (1 - kappa^[6] 0) + g3 * (sig4 * |tX z - q|) := by
      have : 1 - kappa^[4] (tX z) ≤ 1 - kappa^[6] 0 + sig4 * |tX z - q| := by linarith [hch'.1]
      have := mul_le_mul_of_nonneg_left this h3
      linarith
    have t3' : g3 * (1 - kappa^[6] 0) - g3 * (sig4 * |tX z - q|) ≤
        g3 * (1 - kappa^[4] (tX z)) := by
      have : 1 - kappa^[6] 0 - sig4 * |tX z - q| ≤ 1 - kappa^[4] (tX z) := by linarith [hch'.2]
      have := mul_le_mul_of_nonneg_left this h3
      linarith
    have eL : Lc * |tX z - q| = |g1| * |tX z - q| + g2 * |tX z - q| + g3 * (sig4 * |tX z - q|) := by
      rw [hLc]; ring
    have innerabs : |g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) +
        g3 * (1 - kappa^[4] (tX z))| ≤ C0 + Lc * |tX z - q| := by
      rw [abs_le, eL, hC0]
      constructor
      · have hLn : 0 ≤ |g1| * |tX z - q| + g2 * |tX z - q| + g3 * (sig4 * |tX z - q|) := by
          positivity
        have hC00' : 0 ≤ g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - q) + g3 * (1 - kappa^[6] 0) := hC
        linarith
      · linarith
    have hR0 : 0 ≤ C0 + Lc * |tX z - q| := add_nonneg hC00 (mul_nonneg hLc0 habs)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ)),
      abs_of_nonneg hR0]
    exact mul_le_mul_of_nonneg_left innerabs (by positivity)
  -- link 1
  have B1 : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        kernD z.2.2.2 z.2.1 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2) -
          4 / (n : ℝ) * (1 - kappa^[4] (tX z.1)))
      (4 / (n : ℝ) * (C0 + Lc * τ)) := by
    refine L2le.prod' (mK.sub ((measurable_const.sub (hk4.comp mT1)).const_mul _)).aestronglyMeasurable
      hg (Filter.Eventually.of_forall fun z => ?_)
    exact hS (xW z.2 z.1.1) (xW z.2 z.1.2) (normSq_xW hn _ _) (normSq_xW hn _ _)
  -- link 2
  have B2 : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (tX z.1)))
      (4 / (n : ℝ) * (sig4 * τ)) := by
    have h0 : L2le μ1 (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (tX z))) (4 / (n : ℝ) * (sig4 * τ)) := by
      have c0 := (hT.const_mul_nonneg hs4).const_mul_nonneg (c := 4 / (n : ℝ)) (by positivity)
      refine L2le.of_abs_le
        ((measurable_const.sub (hk4.comp mtX)).const_mul _).aestronglyMeasurable c0 (fun z => ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs4, abs_sub_comm]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact iter4_chord (tX_mem hn z)
    exact h0.comp_fst
  have B12 := B1.add0 B2 (by positivity) (by positivity)
  -- transfer to `(u, u′) ⊗ (W, (A, A′, F))`
  have hmap : (μ1.prod P).map MeasurableEquiv.prodAssoc = (lawU2 N).prod (lawR N mW n mA mF) := by
    rw [hμ1, hP, Measure.prodAssoc_prod]
    rfl
  have hf : AEStronglyMeasurable
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      ((μ1.prod P).map MeasurableEquiv.prodAssoc) :=
    (measurable_kD.sub measurable_const).aestronglyMeasurable
  have key : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
          kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (MeasurableEquiv.prodAssoc z))
      (4 / (n : ℝ) * (g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - q) +
        g3 * (1 - kappa^[6] 0) + (|g1| + g2 + g3 * sig4) * τ + sig4 * τ)) := by
    refine (B12.congr_fun fun z => ?_).congr_bound ?_
    · change _ = kernD z.2.2.2 z.2.1 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2) - _
      ring
    · rw [hC0, hLc]; ring
  have h := L2le.of_comp_map (MeasurableEquiv.measurable _) hf key
  rwa [hmap] at h

end General

end BstLean.Part142

open BstLean.Part142 in
#print axioms kernD_fixed_of
open BstLean.Part142 in
#print axioms kernDist_L2_of
open BstLean.Part142 in
#print axioms kernDist_L2_gen
