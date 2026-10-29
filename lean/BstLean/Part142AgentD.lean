import BstLean.Part142Stmt

/-!
# Part 142: the distance form through the Agent network

Role: `delegations/statements/p142-spec.md`, item 2 (sharper kernel bounds). The one-layer links
of the distance form are HYPOTHESES here (the propositions of `Part142Stmt`).

`A = (A₁, A₂, A₃)` has the distribution `mlpGauss n mA n`; `x, x′` are unit vectors,
`t = ⟨x, x′⟩`, `h₁ = ReLU(A₁x)`, `h₂ = ReLU(A₂h₁)`, `A(x) = A₃h₂`, `G = κ∘κ`.

* `agent_phi_L2_of`: `‖Φ_G(A(x), A(x′)) − 2(1 − κ^{∘4}(t))‖₂ ≤
    2·(cA0 + cA1·(1 − κ(κ(t))) + cA2·(1 − t))`.
* `agent_diff_L2_of`: `‖|A(x) − A(x′)|²‖₂ ≤ 4·(dA0 + dA1·(1 − κ(κ(t))) + dA2·(1 − t))`.
* `agent_dlt_L2_of`: `‖(|A(x)| − |A(x′)|)²/2‖₂ ≤ 2·cAdlt`.
* Numbers at `mA n = n²`, `n ≥ 4096`: `cA0 ≤ 0.55/√n`, `cA1 ≤ 1.4143/√n`, `cA2 ≤ 10.7/n`,
  `dA0 ≤ 0.82/n`, `dA1 ≤ 4097/4096`, `dA2 ≤ 10.5/n`, `cAdlt ≤ 7.2/n`.
The helper lemmas are in the namespace `BstLean.Part142.AgD`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

namespace AgD

/-! ## `L²` bounds with a nonnegative bound -/

section tools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `L2le` with a nonnegative bound. -/
def L2nn (μ : Measure Ω) (f : Ω → ℝ) (a : ℝ) : Prop := L2le μ f a ∧ 0 ≤ a

lemma L2nn.add {f g : Ω → ℝ} {a b : ℝ} (h1 : L2nn μ f a) (h2 : L2nn μ g b) :
    L2nn μ (fun ω => f ω + g ω) (a + b) :=
  ⟨h1.1.add0 h2.1 h1.2 h2.2, add_nonneg h1.2 h2.2⟩

lemma L2nn.smul {f : Ω → ℝ} {a : ℝ} (h : L2nn μ f a) {c : ℝ} (hc : 0 ≤ c) :
    L2nn μ (fun ω => c * f ω) (c * a) :=
  ⟨h.1.const_mul_nonneg hc, mul_nonneg hc h.2⟩

lemma L2nn.congr {f g : Ω → ℝ} {a b : ℝ} (h : L2nn μ f a) (hf : ∀ ω, f ω = g ω) (ha : a = b) :
    L2nn μ g b := ⟨(h.1.congr_fun hf).congr_bound ha, ha ▸ h.2⟩

lemma addConst [IsProbabilityMeasure μ] {f : Ω → ℝ} {c a : ℝ}
    (h : L2le μ (fun ω => f ω - c) a) (hc : 0 ≤ c) (ha : 0 ≤ a) : L2nn μ f (c + a) := by
  have h0 : L2le μ (fun _ : Ω => c) c := by
    have := L2le.const (μ := μ) c
    rwa [abs_of_nonneg hc] at this
  exact ⟨(h0.add0 h hc ha).congr_fun fun ω => by ring, add_nonneg hc ha⟩

/-- The shape of the bound of `LinPhiStmt`. -/
lemma comboLin {fN fS fD fL : Ω → ℝ} {aN aS aD aL : ℝ} (hN : L2nn μ fN aN)
    (hS : L2nn μ fS aS) (hD : L2nn μ fD aD) (hL : L2nn μ fL aL) {c i b g k r : ℝ}
    (hc : 0 ≤ c) (hi : 0 ≤ i) (hb : 0 ≤ b) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    L2nn μ (fun ω => c * (fN ω / i + b * fS ω / i + g * (k * fS ω + r * fD ω + 2 * fL ω)))
      (c * (aN / i + b * aS / i + g * (k * aS + r * aD + 2 * aL))) :=
  (((((hN.smul (c := c * (1 / i)) (by positivity)).add
    (hS.smul (c := c * (b / i)) (by positivity))).add
    (hS.smul (c := c * (g * k)) (by positivity))).add
    (hD.smul (c := c * (g * r)) (by positivity))).add
    (hL.smul (c := c * (g * 2)) (by positivity))).congr (fun ω => by ring) (by ring)

/-- The shape of the bound of `ReluPhiStmt`. -/
lemma comboRelu {fE fS fD fL : Ω → ℝ} {aE aS aD aL : ℝ} (hE : L2nn μ fE aE)
    (hS : L2nn μ fS aS) (hD : L2nn μ fD aD) (hL : L2nn μ fL aL) {s e b c g k r : ℝ}
    (hs : 0 ≤ s) (he : 0 ≤ e) (hb : 0 ≤ b) (hc : 0 ≤ c) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (hr : 0 ≤ r) :
    L2nn μ (fun ω => s * (e * fE ω + b * c * fS ω + g * (k * fS ω + r * fD ω + 2 * fL ω)))
      (s * (e * aE + b * c * aS + g * (k * aS + r * aD + 2 * aL))) :=
  (((((hE.smul (c := s * e) (by positivity)).add
    (hS.smul (c := s * (b * c)) (by positivity))).add
    (hS.smul (c := s * (g * k)) (by positivity))).add
    (hD.smul (c := s * (g * r)) (by positivity))).add
    (hL.smul (c := s * (g * 2)) (by positivity))).congr (fun ω => by ring) (by ring)

/-- The shape of the bound of `LinDltStmt` (after the constant is added). -/
lemma comboDlt {fS fD fL : Ω → ℝ} {aS aD aL : ℝ} (hL : L2nn μ fL aL) (hS : L2nn μ fS aS)
    (hD : L2nn μ fD aD) {c k r : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    L2nn μ (fun ω => c * (fL ω + k * fS ω + r * fD ω)) (c * (aL + k * aS + r * aD)) :=
  ((hL.add (hS.smul hk)).add (hD.smul hr)).smul hc

lemma prodNN {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {f : α × β → ℝ} {g : α → ℝ} {a : ℝ}
    (hf : Measurable f) (hg : L2nn μ g a) (h : ∀ x, L2le ν (fun y => f (x, y)) (g x)) :
    L2nn (μ.prod ν) f a :=
  ⟨L2le.prod' hf.aestronglyMeasurable hg.1 (Filter.Eventually.of_forall h), hg.2⟩

end tools

/-! ## Pointwise facts and measurability -/

lemma phiD_nn {ι : Type*} [Fintype ι] {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) :
    0 ≤ phiD G y y' := by
  unfold phiD
  have h1 := psi_le_nrm hG y y'
  have h2 := nrm_mul_le y y'
  linarith

lemma relu_sub_sq (a b : ℝ) : (relu a - relu b) ^ 2 ≤ (a - b) ^ 2 := by
  unfold relu
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]
  · rw [max_eq_right ha, max_eq_left hb]; nlinarith
  · rw [max_eq_left ha, max_eq_right hb]; nlinarith
  · rw [max_eq_left ha, max_eq_left hb]; nlinarith [sq_nonneg (a - b)]

lemma normSq_relu_sub_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (reluV a - reluV b) ≤ normSq (a - b) := by
  unfold normSq
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply, reluV]
  exact relu_sub_sq _ _

lemma normSq_sub_unit {ι : Type*} [Fintype ι] {x x' : ι → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) : normSq (x - x') = 2 * (1 - dotp x x') := by
  have h := eD_eq x x'
  unfold eD at h
  rw [hx, hx'] at h
  linarith

lemma dlt_unit {ι : Type*} [Fintype ι] {x x' : ι → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) : dlt x x' = 0 := by
  unfold dlt
  rw [nrm_of_normSq_one hx, nrm_of_normSq_one hx', hx, hx']
  norm_num

lemma sconv {m : ℝ} (c a : ℝ) : c * √m * a = m * (c / √m * a) := by
  calc c * √m * a = c * (m / √m) * a := by rw [Real.div_sqrt]
    _ = m * (c / √m * a) := by ring

section meas

variable {k : ℕ}

lemma m_phiD {G : ℝ → ℝ} (hG : Continuous G) :
    Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => phiD G p.1 p.2) := by
  unfold phiD
  exact (((continuous_normSq.comp continuous_fst).add
    (continuous_normSq.comp continuous_snd)).measurable.div_const 2).sub (measurable_psi hG)

lemma m_dlt : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => dlt p.1 p.2) := by
  unfold dlt
  exact ((((continuous_normSq.comp continuous_fst).add
    (continuous_normSq.comp continuous_snd)).div_const 2).sub
    ((continuous_nrm.comp continuous_fst).mul (continuous_nrm.comp continuous_snd))).measurable

lemma m_nsub : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => normSq (p.1 - p.2)) :=
  (continuous_normSq.comp (continuous_fst.sub continuous_snd)).measurable

lemma m_absd : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => |normSq p.1 - normSq p.2|) :=
  (((continuous_normSq.comp continuous_fst).sub
    (continuous_normSq.comp continuous_snd)).abs).measurable

lemma mPair {Ω : Type*} [MeasurableSpace Ω] {F : (Fin k → ℝ) × (Fin k → ℝ) → ℝ}
    (hF : Measurable F) {a b : Ω → Fin k → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => F (a ω, b ω)) := hF.comp (ha.prodMk hb)

lemma mR {m : ℕ} (h : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h)) :=
  measurable_reluV.comp (measurable_mulVec_right h)

end meas

/-! ## One layer, general inputs -/

section gen

variable {m k : ℕ} {v : ℝ}

lemma genSq (hv : 0 < v) (hm : 1 ≤ m) (h : Fin k → ℝ) :
    L2nn (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (reluV (M.mulVec h)))
      ((m : ℝ) / 2 * v * (√(1 + 5 / (m : ℝ)) * normSq h)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := normSq_nonneg h
  obtain ⟨hi, he⟩ := layer_relu_four (m := m) hv.le h
  refine ⟨L2le.mk' (measurable_normSq.comp (mR h)).aestronglyMeasurable hi (le_of_eq ?_),
    by positivity⟩
  rw [he]
  have hq : √(1 + 5 / (m : ℝ)) ^ 2 = 1 + 5 / (m : ℝ) := Real.sq_sqrt (by positivity)
  have e : ((m : ℝ) / 2 * v * (√(1 + 5 / (m : ℝ)) * normSq h)) ^ 2 =
      ((m : ℝ) / 2 * v) ^ 2 * normSq h ^ 2 * √(1 + 5 / (m : ℝ)) ^ 2 := by ring
  have h5 : (5 : ℝ) / m * m = 5 := by field_simp
  rw [e, hq]
  linear_combination (-((m : ℝ) / 4 * v ^ 2 * normSq h ^ 2)) * h5

lemma genS (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (reluV (M.mulVec h)) + normSq (reluV (M.mulVec h')))
      ((m : ℝ) / 2 * v * (√(1 + 5 / (m : ℝ)) * (normSq h + normSq h'))) :=
  ((genSq hv hm h).add (genSq hv hm h')).congr (fun _ => rfl) (by ring)

lemma genD (hRS : ReluSqStmt) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        |normSq (reluV (M.mulVec h)) - normSq (reluV (M.mulVec h'))|)
      ((m : ℝ) / 2 * v * (√5 / √(m : ℝ) * (normSq h + normSq h') +
        |normSq h - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := normSq_nonneg h
  have hN' := normSq_nonneg h'
  have hs : 0 ≤ (m : ℝ) / 2 * v := by positivity
  obtain ⟨a1, -⟩ := hRS hv hm h
  obtain ⟨a2, -⟩ := hRS hv hm h'
  have hc := L2le.const (μ := gaussMat m k v)
    ((m : ℝ) / 2 * (v * normSq h) - (m : ℝ) / 2 * (v * normSq h'))
  have hsum := (a1.add0 a2.neg (by positivity) (by positivity)).add0 hc (by positivity)
    (abs_nonneg _)
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      |normSq (reluV (M.mulVec h)) - normSq (reluV (M.mulVec h'))|) :=
    mPair m_absd (mR h) (mR h')
  refine ⟨(L2le.of_abs_le hmeas.aestronglyMeasurable hsum (fun M => ?_)).congr_bound ?_,
    by positivity⟩
  · rw [abs_abs]
    apply le_of_eq
    congr 1
    ring
  · have e : (m : ℝ) / 2 * (v * normSq h) - (m : ℝ) / 2 * (v * normSq h') =
        (m : ℝ) / 2 * v * (normSq h - normSq h') := by ring
    rw [e, abs_mul, abs_of_nonneg hs, sconv (√5 / 2) (v * normSq h),
      sconv (√5 / 2) (v * normSq h')]
    ring

lemma genN (hRE : ReluEDStmt) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (reluV (M.mulVec h) - reluV (M.mulVec h')))
      ((m : ℝ) / 2 * v * (2 * phiD kappa h h' + 2 * √3 / √(m : ℝ) * normSq (h - h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hP := phiD_nn kGood_kappa h h'
  have hE := normSq_nonneg (h - h')
  have h1 := (addConst (hRE hv hm h h') (by positivity) (by positivity)).smul
    (c := 2) (by norm_num)
  refine h1.congr (fun M => ?_) ?_
  · rw [eD_eq]; ring
  · have e : √3 / 2 * √(m : ℝ) * v * normSq (h - h') =
        √3 / 2 * √(m : ℝ) * (v * normSq (h - h')) := by ring
    rw [e, sconv (√3 / 2) (v * normSq (h - h'))]
    ring

lemma genL (hRD : ReluDltStmt) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => dlt (reluV (M.mulVec h)) (reluV (M.mulVec h')))
      ((m : ℝ) / 2 * v * (dlt h h' + 4 * Kr m / (m : ℝ) * (normSq h + normSq h') +
        √5 / √(m : ℝ) * |normSq h - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := normSq_nonneg h
  have hN' := normSq_nonneg h'
  have hd := dlt_nonneg h h'
  have hK := Kr_nonneg m
  exact (addConst (hRD hv hm h h') (by positivity) (by positivity)).congr (fun _ => rfl)
    (by ring)

lemma linN (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (M.mulVec h - M.mulVec h'))
      ((m : ℝ) * v * (√(1 + 2 / (m : ℝ)) * normSq (h - h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hE := normSq_nonneg (h - h')
  obtain ⟨hi, he⟩ := layer_lin_four (m := m) hv.le (h - h')
  have hf : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      normSq (M.mulVec h - M.mulVec h') = normSq (M.mulVec (h - h')) := fun M => by
    rw [Matrix.mulVec_sub]
  simp_rw [hf]
  refine ⟨L2le.mk' (measurable_normSq.comp (measurable_mulVec_right _)).aestronglyMeasurable hi
    (le_of_eq ?_), by positivity⟩
  rw [he]
  have hq : √(1 + 2 / (m : ℝ)) ^ 2 = 1 + 2 / (m : ℝ) := Real.sq_sqrt (by positivity)
  have e : ((m : ℝ) * v * (√(1 + 2 / (m : ℝ)) * normSq (h - h'))) ^ 2 =
      ((m : ℝ) * v) ^ 2 * normSq (h - h') ^ 2 * √(1 + 2 / (m : ℝ)) ^ 2 := by ring
  have h2 : (2 : ℝ) / m * m = 2 := by field_simp
  rw [e, hq]
  linear_combination (-((m : ℝ) * v ^ 2 * normSq (h - h') ^ 2)) * h2

lemma linL (hLD : LinDltStmt) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => dlt (M.mulVec h) (M.mulVec h'))
      ((m : ℝ) * v * (dlt h h' + K4 m / (m : ℝ) * (normSq h + normSq h') +
        √2 / √(m : ℝ) * |normSq h - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := normSq_nonneg h
  have hN' := normSq_nonneg h'
  have hd := dlt_nonneg h h'
  have hK := K4_nonneg m
  exact (addConst (hLD hv hm h h') (by positivity) (by positivity)).congr (fun _ => rfl)
    (by ring)

end gen

/-! ## The constants (without the scale factors) -/

/-- The constant part of the bound of `Φ_κ(h₁, h₁′)`. -/
noncomputable def nc0 (m : ℕ) : ℝ := bG kappa * √5 / √(m : ℝ) + kappa 0 * (8 * Kr m / (m : ℝ))

noncomputable def pS (m : ℕ) (τ u : ℝ) : ℝ := τ + 2 * √3 / √(m : ℝ) * u + nc0 m
noncomputable def eS (m : ℕ) (u : ℝ) : ℝ := 4 * √(1 + 2 / (m : ℝ)) * u
noncomputable def sS (m : ℕ) : ℝ := 2 * √(1 + 5 / (m : ℝ))
noncomputable def dS (m : ℕ) : ℝ := 2 * √5 / √(m : ℝ)
noncomputable def lS (m : ℕ) : ℝ := 8 * Kr m / (m : ℝ)
noncomputable def NS (m : ℕ) (τ u : ℝ) : ℝ := 2 * pS m τ u + 2 * √3 / √(m : ℝ) * eS m u
noncomputable def SS (m : ℕ) : ℝ := √(1 + 5 / (m : ℝ)) * sS m
noncomputable def DS (m : ℕ) : ℝ := √5 / √(m : ℝ) * sS m + dS m
noncomputable def LS (m : ℕ) : ℝ :=
  lS m + 4 * Kr m / (m : ℝ) * sS m + √5 / √(m : ℝ) * dS m

noncomputable def q1 (n m : ℕ) (τ u : ℝ) : ℝ :=
  NS m τ u / √(2 * (n : ℝ)) + bG (kappa ∘ kappa) * SS m / √(2 * (n : ℝ)) +
    (kappa ∘ kappa) 0 * (K4 n / (n : ℝ) * SS m + √2 / √(n : ℝ) * DS m + 2 * LS m)

noncomputable def q2 (m : ℕ) (u : ℝ) : ℝ :=
  √3 / √(m : ℝ) * eS m u + bG (kappa ∘ kappa) * (√5 / (2 * √(m : ℝ))) * sS m +
    (kappa ∘ kappa) 0 * (4 * Kr m / (m : ℝ) * sS m + √5 / √(m : ℝ) * dS m + 2 * lS m)

noncomputable def q3 (m : ℕ) (u : ℝ) : ℝ :=
  √3 / √(m : ℝ) * (2 * u) + bG ((kappa ∘ kappa) ∘ kappa) * (√5 / (2 * √(m : ℝ))) * (1 + 1) +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr m / (m : ℝ) * (1 + 1) + √5 / √(m : ℝ) * 0 + 2 * 0)

noncomputable def qA (n m : ℕ) (τ u : ℝ) : ℝ := q1 n m τ u + q2 m u + q3 m u

/-! ## The first hidden layer at unit inputs -/

section layer1

variable {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ} (hx : normSq x = 1)
  (hx' : normSq x' = 1)

include hx hx' in
lemma tau_nonneg : 0 ≤ 1 - kappa (kappa (dotp x x')) ∧ 0 ≤ 1 - dotp x x' := by
  have ht := dotp_unit_mem hx hx'
  have := (kk_memIcc ht).2
  exact ⟨by linarith, by linarith [ht.2]⟩

include hn hm hx hx'

lemma l1P (hRP : ReluPhiStmt) :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ => phiD kappa (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * pS m (1 - kappa (kappa (dotp x x'))) (1 - dotp x x')) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hb := bG_nonneg kGood_kappa
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  have hKr := Kr_nonneg m
  have h0 := hRP kGood_kappa (v := 2 / (n : ℝ)) (by positivity) hm x x'
  have hph : phiD (kappa ∘ kappa) x x' = 1 - kappa (kappa (dotp x x')) := by
    rw [phiD_unit _ hx hx']; rfl
  rw [hph, normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at h0
  refine (addConst h0 (by positivity) (by positivity)).congr (fun _ => rfl) ?_
  unfold pS nc0
  ring

lemma l1E :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ => normSq (reluV (M.mulVec x) - reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * eS m (1 - dotp x x')) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  obtain ⟨hi, he⟩ := layer_lin_four (m := m) (v := 2 / (n : ℝ)) (by positivity) (x - x')
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ =>
      normSq (reluV (M.mulVec x) - reluV (M.mulVec x'))) := mPair m_nsub (mR x) (mR x')
  unfold eS
  refine ⟨L2le.of_sq_le hmeas.aestronglyMeasurable hi (fun M => ?_) (le_of_eq ?_),
    by positivity⟩
  · have h1 := normSq_relu_sub_le (M.mulVec x) (M.mulVec x')
    rw [← Matrix.mulVec_sub] at h1
    exact pow_le_pow_left₀ (normSq_nonneg _) h1 2
  · rw [he, normSq_sub_unit hx hx']
    have hq : √(1 + 2 / (m : ℝ)) ^ 2 = 1 + 2 / (m : ℝ) := Real.sq_sqrt (by positivity)
    have h2 : (2 : ℝ) / m * m = 2 := by field_simp
    have e : ((m : ℝ) / 2 * (2 / (n : ℝ)) * (4 * √(1 + 2 / (m : ℝ)) * (1 - dotp x x'))) ^ 2 =
        ((m : ℝ) / 2 * (2 / (n : ℝ))) ^ 2 * 16 * (1 - dotp x x') ^ 2 *
          √(1 + 2 / (m : ℝ)) ^ 2 := by ring
    rw [e, hq]
    linear_combination (-(16 * (1 - dotp x x') ^ 2 * (m : ℝ) / (n : ℝ) ^ 2)) * h2

lemma l1S :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        normSq (reluV (M.mulVec x)) + normSq (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * sS m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := genS (m := m) (v := 2 / (n : ℝ)) (by positivity) hm x x'
  rw [hx, hx'] at h
  refine h.congr (fun _ => rfl) ?_
  unfold sS
  ring

lemma l1D (hRS : ReluSqStmt) :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        |normSq (reluV (M.mulVec x)) - normSq (reluV (M.mulVec x'))|)
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * dS m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := genD hRS (m := m) (v := 2 / (n : ℝ)) (by positivity) hm x x'
  rw [hx, hx', sub_self, abs_zero] at h
  refine h.congr (fun _ => rfl) ?_
  unfold dS
  ring

lemma l1L (hRD : ReluDltStmt) :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ => dlt (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * lS m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := genL hRD (m := m) (v := 2 / (n : ℝ)) (by positivity) hm x x'
  rw [dlt_unit hx hx', hx, hx', sub_self, abs_zero] at h
  refine h.congr (fun _ => rfl) ?_
  unfold lS
  ring

end layer1

end AgD

open AgD

/-! ## The constants of the statements -/

/-- The constant term of `agent_phi_L2_of`. -/
noncomputable def cA0 (n mA : ℕ) : ℝ := qA n mA 0 0
/-- The coefficient of `1 − κ(κ(t))` in `agent_phi_L2_of`. -/
noncomputable def cA1 (n mA : ℕ) : ℝ := qA n mA 1 0 - qA n mA 0 0
/-- The coefficient of `1 − t` in `agent_phi_L2_of`. -/
noncomputable def cA2 (n mA : ℕ) : ℝ := qA n mA 0 1 - qA n mA 0 0

noncomputable def dA0 (n mA : ℕ) : ℝ := √(1 + 2 / (n : ℝ)) * nc0 mA
noncomputable def dA1 (n _mA : ℕ) : ℝ := √(1 + 2 / (n : ℝ))
noncomputable def dA2 (n mA : ℕ) : ℝ :=
  √(1 + 2 / (n : ℝ)) * (2 * √3 / √(mA : ℝ) + √3 / √(mA : ℝ) * (4 * √(1 + 2 / (mA : ℝ))))

noncomputable def cAdlt (n mA : ℕ) : ℝ := LS mA + K4 n / (n : ℝ) * SS mA + √2 / √(n : ℝ) * DS mA

lemma qA_affine (n m : ℕ) (τ u : ℝ) : qA n m τ u = cA0 n m + cA1 n m * τ + cA2 n m * u := by
  unfold cA0 cA1 cA2 qA q1 q2 q3 NS pS eS
  ring

lemma cA1_eq (n m : ℕ) : cA1 n m = 2 / √(2 * (n : ℝ)) := by
  unfold cA1 qA q1 q2 q3 NS pS eS
  ring

lemma cA2_eq (n m : ℕ) : cA2 n m =
    (2 * (2 * √3 / √(m : ℝ)) + 2 * √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ)))) / √(2 * (n : ℝ)) +
      √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ))) + √3 / √(m : ℝ) * 2 := by
  unfold cA2 qA q1 q2 q3 NS pS eS
  ring

lemma cA0_eq (n m : ℕ) : cA0 n m =
    2 * nc0 m / √(2 * (n : ℝ)) + bG (kappa ∘ kappa) * SS m / √(2 * (n : ℝ)) +
      (kappa ∘ kappa) 0 * (K4 n / (n : ℝ) * SS m + √2 / √(n : ℝ) * DS m + 2 * LS m) +
      (bG (kappa ∘ kappa) * (√5 / (2 * √(m : ℝ))) * sS m +
        (kappa ∘ kappa) 0 * (4 * Kr m / (m : ℝ) * sS m + √5 / √(m : ℝ) * dS m + 2 * lS m)) +
      (bG ((kappa ∘ kappa) ∘ kappa) * (√5 / (2 * √(m : ℝ))) * 2 +
        ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr m / (m : ℝ) * 2)) := by
  unfold cA0 qA q1 q2 q3 NS pS eS
  ring

/-! ## The three statements -/

section main

variable {n m : ℕ}

/-- **The distance form through the Agent network.** -/
theorem agent_phi_L2_of (hRS : ReluSqStmt) (hRE : ReluEDStmt) (hRD : ReluDltStmt)
    (hRP : ReluPhiStmt) (hLP : LinPhiStmt) (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')))
      (2 * (cA0 n m + cA1 n m * (1 - kappa (kappa (dotp x x'))) +
        cA2 n m * (1 - dotp x x'))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb2 := bG_nonneg hG
  have hb3 := bG_nonneg hGk
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hKm := Kr_nonneg m
  have hK4 := K4_nonneg n
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hi : (0 : ℝ) ≤ √(2 * (n : ℝ)) := Real.sqrt_nonneg _
  have hk : (0 : ℝ) ≤ K4 n / (n : ℝ) := by positivity
  have hr : (0 : ℝ) ≤ √2 / √(n : ℝ) := by positivity
  have he : (0 : ℝ) ≤ 2 * √3 / √(m : ℝ) := by positivity
  have he3 : (0 : ℝ) ≤ √3 / √(m : ℝ) := by positivity
  have hq5 : (0 : ℝ) ≤ √(1 + 5 / (m : ℝ)) := Real.sqrt_nonneg _
  have he5 : (0 : ℝ) ≤ √5 / √(m : ℝ) := by positivity
  have hc5 : (0 : ℝ) ≤ √5 / (2 * √(m : ℝ)) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have hc2e : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have h31 : (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ))) = 2 := by field_simp
  -- the first hidden layer
  have aP := l1P hn hm hx hx' hRP
  have aE := l1E hn hm hx hx'
  have aS := l1S hn hm hx hx'
  have aD := l1D hn hm hx hx' hRS
  have aL := l1L hn hm hx hx' hRD
  -- the bounds of the second hidden layer, as functions of the first matrix
  have N1 := ((aP.smul (c := 2) (by norm_num)).add (aE.smul he)).smul hc2
  have S1 := (aS.smul hq5).smul hc2
  have D1 := ((aS.smul he5).add aD).smul hc2
  have L1 := ((aL.add (aS.smul hk4)).add (aD.smul he5)).smul hc2
  -- measurability
  have mH2 : ∀ z : Fin n → ℝ, Measurable (fun A : MlpParam n m n =>
      reluV (A.2.1.mulVec (reluV (A.1.mulVec z)))) := fun z =>
    (continuous_reluV.comp (Continuous.matrix_mulVec (continuous_fst.comp continuous_snd)
      (continuous_reluV.comp
        (Continuous.matrix_mulVec continuous_fst continuous_const)))).measurable
  have mH1 : ∀ z : Fin n → ℝ, Measurable (fun A : MlpParam n m n =>
      reluV (A.1.mulVec z)) := fun z =>
    (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const)).measurable
  have mf1 : Measurable (fun A : MlpParam n m n =>
      phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        (n : ℝ) * (2 / (m : ℝ)) * phiD (kappa ∘ kappa)
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x))))
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x'))))) :=
    (mPair (m_phiD hG.cont) (measurable_mlpEval_param x) (measurable_mlpEval_param x')).sub
      ((mPair (m_phiD hG.cont) (mH2 x) (mH2 x')).const_mul _)
  have mf2 : Measurable (fun A : MlpParam n m n =>
      (n : ℝ) * (2 / (m : ℝ)) * (phiD (kappa ∘ kappa)
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x))))
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x')))) -
        (m : ℝ) / 2 * (2 / (m : ℝ)) * phiD ((kappa ∘ kappa) ∘ kappa)
          (reluV (A.1.mulVec x)) (reluV (A.1.mulVec x')))) :=
    ((mPair (m_phiD hG.cont) (mH2 x) (mH2 x')).sub
      ((mPair (m_phiD hGk.cont) (mH1 x) (mH1 x')).const_mul _)).const_mul _
  -- the last matrix
  have G1 := comboLin N1 S1 D1 L1 hc3 hi hb2 hg2 hk hr
  have T1 := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf1 G1
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf1.comp measurable_prodMk_left)
      (comboLin (genN hRE hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genD hRS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genL hRD hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hi hb2 hg2 hk hr)
      (fun M₂ => hLP hG hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x')))) (dotp_relu_nonneg _ _))).1)
  -- the second matrix
  have G2 := (comboRelu aE aS aD aL hc2 he3 hb2 hc5 hg2 hk4 he5).smul hc3
  have T2 := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf2 G2
    (fun M₁ => ((hRP hG hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))).const_mul_nonneg
      hc3).comp_fst)
  -- the first matrix
  have h3 := hRP hGk hv1 hm x x'
  rw [normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at h3
  have T3 := ((h3.const_mul_nonneg hc2).const_mul_nonneg hc3).comp_fst
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ))))
  have n3 : 0 ≤ (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (m : ℝ)) *
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * (√3 / √(m : ℝ) * (2 * (1 - dotp x x')) +
        bG ((kappa ∘ kappa) ∘ kappa) * (√5 / (2 * √(m : ℝ))) * (1 + 1) +
        ((kappa ∘ kappa) ∘ kappa) 0 *
          (4 * Kr m / (m : ℝ) * (1 + 1) + √5 / √(m : ℝ) * 0 + 2 * 0)))) := by positivity
  have hsum := (T1.1.add0 T2.1 T1.2 T2.2).add0 T3 (add_nonneg T1.2 T2.2) n3
  have hph : phiD (((kappa ∘ kappa) ∘ kappa) ∘ kappa) x x' = 1 - kappa^[4] (dotp x x') := by
    rw [phiD_unit _ hx hx']; rfl
  rw [← qA_affine]
  unfold mlpGauss
  refine (hsum.congr_fun fun A => ?_).congr_bound ?_
  · rw [hph]
    linear_combination (-((1 - kappa^[4] (dotp x x')) * ((n : ℝ) * (2 / (m : ℝ))) *
      ((m : ℝ) / 2 * (2 / (n : ℝ))))) * hc2e + (-(1 - kappa^[4] (dotp x x'))) * h31
  · linear_combination (norm := (unfold qA q1 q2 q3 NS SS DS LS; ring1))
      (qA n m (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') * ((n : ℝ) * (2 / (m : ℝ))) *
        ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
      qA n m (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') * h31

/-- **The squared distance of the two outputs of the Agent network.** -/
theorem agent_diff_L2_of (hRE : ReluEDStmt) (hRP : ReluPhiStmt) (hn : 1 ≤ n) (hm : 1 ≤ m)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (dA0 n m + dA1 n m * (1 - kappa (kappa (dotp x x'))) +
        dA2 n m * (1 - dotp x x'))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have he : (0 : ℝ) ≤ 2 * √3 / √(m : ℝ) := by positivity
  have hq : (0 : ℝ) ≤ √(1 + 2 / (n : ℝ)) := Real.sqrt_nonneg _
  have hc2e : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have h31 : (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ))) = 2 := by field_simp
  have aP := l1P hn hm hx hx' hRP
  have aE := l1E hn hm hx hx'
  have N1 := ((((aP.smul (c := 2) (by norm_num)).add (aE.smul he)).smul hc2).smul hq).smul hc3
  have mf : Measurable (fun A : MlpParam n m n => normSq (mlpEval A x - mlpEval A x')) :=
    mPair m_nsub (measurable_mlpEval_param x) (measurable_mlpEval_param x')
  have T := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf N1
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf.comp measurable_prodMk_left)
      (((genN hRE hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))).smul hq).smul hc3)
      (fun M₂ => (linN hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x'))))).1)).1)
  unfold mlpGauss
  refine T.1.congr_bound ?_
  linear_combination (norm := (unfold dA0 dA1 dA2 pS eS; ring1))
    (2 * (dA0 n m + dA1 n m * (1 - kappa (kappa (dotp x x'))) + dA2 n m * (1 - dotp x x')) *
      ((n : ℝ) * (2 / (m : ℝ))) * ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
    (2 * (dA0 n m + dA1 n m * (1 - kappa (kappa (dotp x x'))) + dA2 n m * (1 - dotp x x'))) *
      h31

/-- **The term `δ` of the two outputs of the Agent network.** -/
theorem agent_dlt_L2_of (hRS : ReluSqStmt) (hRD : ReluDltStmt) (hLD : LinDltStmt) (hn : 1 ≤ n)
    (hm : 1 ≤ m) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => dlt (mlpEval A x) (mlpEval A x')) (2 * cAdlt n m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hKm := Kr_nonneg m
  have hK4 := K4_nonneg n
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hk : (0 : ℝ) ≤ K4 n / (n : ℝ) := by positivity
  have hr : (0 : ℝ) ≤ √2 / √(n : ℝ) := by positivity
  have hq5 : (0 : ℝ) ≤ √(1 + 5 / (m : ℝ)) := Real.sqrt_nonneg _
  have he5 : (0 : ℝ) ≤ √5 / √(m : ℝ) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have hc2e : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have h31 : (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ))) = 2 := by field_simp
  have aS := l1S hn hm hx hx'
  have aD := l1D hn hm hx hx' hRS
  have aL := l1L hn hm hx hx' hRD
  have S1 := (aS.smul hq5).smul hc2
  have D1 := ((aS.smul he5).add aD).smul hc2
  have L1 := ((aL.add (aS.smul hk4)).add (aD.smul he5)).smul hc2
  have G1 := comboDlt L1 S1 D1 hc3 hk hr
  have mf : Measurable (fun A : MlpParam n m n => dlt (mlpEval A x) (mlpEval A x')) :=
    mPair m_dlt (measurable_mlpEval_param x) (measurable_mlpEval_param x')
  have T := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf G1
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf.comp measurable_prodMk_left)
      (comboDlt (genL hRD hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genD hRS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hk hr)
      (fun M₂ => (linL hLD hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x'))))).1)).1)
  unfold mlpGauss
  refine T.1.congr_bound ?_
  linear_combination (norm := (unfold cAdlt LS SS DS; ring1))
    (cAdlt n m * ((n : ℝ) * (2 / (m : ℝ))) * ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
    cAdlt n m * h31

end main

/-! ## Nonnegativity of the constants -/

namespace AgD

lemma nc0_nn (m : ℕ) : 0 ≤ nc0 m := by
  have hb := bG_nonneg kGood_kappa
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  have hKr := Kr_nonneg m
  unfold nc0
  positivity

lemma sS_nn (m : ℕ) : 0 ≤ sS m := by unfold sS; positivity
lemma dS_nn (m : ℕ) : 0 ≤ dS m := by unfold dS; positivity
lemma lS_nn (m : ℕ) : 0 ≤ lS m := by have := Kr_nonneg m; unfold lS; positivity
lemma SS_nn (m : ℕ) : 0 ≤ SS m := by have := sS_nn m; unfold SS; positivity
lemma DS_nn (m : ℕ) : 0 ≤ DS m := by
  have := sS_nn m; have := dS_nn m; unfold DS; positivity
lemma LS_nn (m : ℕ) : 0 ≤ LS m := by
  have := sS_nn m; have := dS_nn m; have := lS_nn m; have := Kr_nonneg m
  unfold LS; positivity

end AgD

lemma cA0_nonneg (n m : ℕ) : 0 ≤ cA0 n m := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb2 := bG_nonneg hG
  have hb3 := bG_nonneg hGk
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have := nc0_nn m; have := sS_nn m; have := dS_nn m; have := lS_nn m
  have := SS_nn m; have := DS_nn m; have := LS_nn m
  have := Kr_nonneg m; have := K4_nonneg n
  rw [cA0_eq]
  positivity

lemma cA1_nonneg (n m : ℕ) : 0 ≤ cA1 n m := by rw [cA1_eq]; positivity
lemma cA2_nonneg (n m : ℕ) : 0 ≤ cA2 n m := by rw [cA2_eq]; positivity
lemma dA0_nonneg (n m : ℕ) : 0 ≤ dA0 n m := by have := nc0_nn m; unfold dA0; positivity
lemma dA1_nonneg (n m : ℕ) : 0 ≤ dA1 n m := by unfold dA1; positivity
lemma dA2_nonneg (n m : ℕ) : 0 ≤ dA2 n m := by unfold dA2; positivity
lemma cAdlt_nonneg (n m : ℕ) : 0 ≤ cAdlt n m := by
  have := SS_nn m; have := DS_nn m; have := LS_nn m; have := K4_nonneg n
  unfold cAdlt; positivity

/-! ## The numbers at the width `mA n = n²`, `n ≥ 4096` -/

namespace AgD

lemma sqrt5_le' : √(5 : ℝ) ≤ 223607 / 100000 := sqrt_le_of_sq (by norm_num) (by norm_num)

lemma b2_le : bG (kappa ∘ kappa) ≤ 33087 / 100000 := by
  unfold bG
  simp only [Function.comp_apply, kappa_neg_one]
  have := kappa2_zero_ge
  have := kappa_zero_le
  linarith

lemma g2_le : (kappa ∘ kappa) 0 ≤ 49376 / 100000 := by
  simp only [Function.comp_apply]
  exact kappa2_zero_le

lemma b3_le : bG ((kappa ∘ kappa) ∘ kappa) ≤ 28416 / 100000 := by
  unfold bG
  simp only [Function.comp_apply, kappa_neg_one]
  have := kappa3_zero_ge
  have := kappa2_zero_le
  linarith

lemma g3_le : ((kappa ∘ kappa) ∘ kappa) 0 ≤ 1 := by
  simp only [Function.comp_apply]
  exact kappa3_zero_le_one

lemma bk_le : bG kappa ≤ 363382 / 1000000 := by
  unfold bG
  rw [kappa_neg_one]
  have := kappa_zero_ge
  linarith

section focus

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

lemma nsq_ge : (4096 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hx := nR_ge hn
  nlinarith

lemma Kr_mA_le : Kr (mA n) ≤ 11 / 5 := by
  have h2 := nsq_ge hn
  unfold Kr
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 35 / (n : ℝ) ^ 2 ≤ 35 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have e : ((11 : ℝ) / 5) ^ 2 = 121 / 25 := by norm_num
  rw [e]
  linarith

lemma Q5_le : √(1 + 5 / (mA n : ℝ)) ≤ 1001 / 1000 := by
  have h2 := nsq_ge hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 5 / (n : ℝ) ^ 2 ≤ 5 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have e : ((1001 : ℝ) / 1000) ^ 2 = 1002001 / 1000000 := by norm_num
  rw [e]
  linarith

lemma Q2_le : √(1 + 2 / (mA n : ℝ)) ≤ 1001 / 1000 := by
  have h2 := nsq_ge hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 2 / (n : ℝ) ^ 2 ≤ 2 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have e : ((1001 : ℝ) / 1000) ^ 2 = 1002001 / 1000000 := by norm_num
  rw [e]
  linarith

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)`. -/
lemma yzr : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 4096 ∧ z ≤ 1 / 64 ∧ r ≤ 707107 / 1000000 * z ∧
    r ≤ 1 / 90 ∧ y = z * z := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have h90 : (90 : ℝ) ≤ √(2 * (n : ℝ)) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    by positivity, by positivity, one_div_le_one_div_of_le (by norm_num) hx,
    one_div_le_one_div_of_le (by norm_num) hs, ?_, one_div_le_one_div_of_le (by norm_num) h90,
    ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]

lemma sS_le : sS (mA n) ≤ 2002 / 1000 := by
  have := Q5_le hn
  unfold sS
  linarith

lemma SS_le : SS (mA n) ≤ 2005 / 1000 := by
  have h1 := Q5_le hn
  have h2 := sS_le hn
  have h3 := sS_nn (mA n)
  unfold SS
  calc √(1 + 5 / (mA n : ℝ)) * sS (mA n) ≤ 1001 / 1000 * (2002 / 1000) := by gcongr
    _ ≤ 2005 / 1000 := by norm_num

lemma dS_le : dS (mA n) ≤ 447214 / 100000 * (1 / (n : ℝ)) := by
  have h5 := sqrt5_le'
  have hx := nR_ge hn
  have hy : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold dS
  rw [sqrt_mA]
  have e : 2 * √5 / (n : ℝ) = 2 * √5 * (1 / (n : ℝ)) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) hy

lemma DS_le : DS (mA n) ≤ 895 / 100 * (1 / (n : ℝ)) := by
  have h5 := sqrt5_le'
  have hx := nR_ge hn
  have h2 := sS_le hn
  have h3 := sS_nn (mA n)
  have h4 := dS_le hn
  unfold DS
  rw [sqrt_mA]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  rw [← hy] at h4 ⊢
  refine le_trans (le_of_eq (?_ : _ = √5 * y * sS (mA n) + dS (mA n))) ?_
  · rw [hy]; ring
  · calc √5 * y * sS (mA n) + dS (mA n)
        ≤ 223607 / 100000 * y * (2002 / 1000) + 447214 / 100000 * y := by gcongr
      _ ≤ 895 / 100 * y := by linarith

lemma lS_le : lS (mA n) ≤ 176 / 10 * (1 / (n : ℝ)) ^ 2 := by
  have hK := Kr_mA_le hn
  have hx := nR_ge hn
  have hy : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ 2 := by positivity
  unfold lS
  rw [mA_eqR]
  have e : 8 * Kr (mA n) / (n : ℝ) ^ 2 = 8 * Kr (mA n) * (1 / (n : ℝ)) ^ 2 := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) hy

lemma LS_le : LS (mA n) ≤ 12 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn
  have hK0 := Kr_nonneg (mA n)
  have h2 := sS_le hn
  have h3 := sS_nn (mA n)
  have h4 := dS_le hn
  have h4n := dS_nn (mA n)
  have h6 := lS_le hn
  unfold LS
  rw [sqrt_mA, mA_eqR]
  rw [← hy] at h4 h6 ⊢
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = lS (mA n) + 4 * Kr (mA n) * y ^ 2 * sS (mA n) +
    √5 * y * dS (mA n))) ?_
  · rw [hy]; ring
  · calc lS (mA n) + 4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n)
        ≤ 176 / 10 * y ^ 2 + 4 * (11 / 5) * y ^ 2 * (2002 / 1000) +
          223607 / 100000 * y * (447214 / 100000 * y) := by gcongr
      _ ≤ 12 / 1000 * y := by nlinarith

lemma nc0_le : nc0 (mA n) ≤ 815 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn
  have hK0 := Kr_nonneg (mA n)
  have hb := bk_le
  have hb0 := bG_nonneg kGood_kappa
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  unfold nc0
  rw [sqrt_mA, mA_eqR]
  rw [← hy]
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2))) ?_
  · rw [hy]; ring
  · calc bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2)
        ≤ 363382 / 1000000 * (223607 / 100000) * y +
          31831 / 100000 * (8 * (11 / 5) * y ^ 2) := by gcongr
      _ ≤ 815 / 1000 * y := by nlinarith

end focus

end AgD

section focusBounds

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `cA1 ≤ 1.4143/√n`. -/
theorem cA1_le : cA1 n (mA n) ≤ 14143 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  rw [cA1_eq]
  refine le_trans (le_of_eq (?_ : _ = 2 * r)) ?_
  · rw [hr]; ring
  · refine le_trans (?_ : _ ≤ 14143 / 10000 * z) (le_of_eq ?_)
    · linarith
    · rw [hz]; ring

/-- `cA2 ≤ 10.7/n`. -/
theorem cA2_le : cA2 n (mA n) ≤ 107 / 10 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h3 := sqrt3_le
  have hQ := Q2_le hn
  have hyr : y * r ≤ y * (1 / 90) := mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [cA2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (2 * (2 * √3 * y) + 2 * √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))) * r + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) + √3 * y * 2)) ?_
  · rw [hy, hr]; ring
  · refine le_trans (?_ : _ ≤ 107 / 10 * y) (le_of_eq (by rw [hy]; ring))
    calc (2 * (2 * √3 * y) + 2 * √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * r +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) + √3 * y * 2
        ≤ (2 * (2 * (17321 / 10000) * y) + 2 * (17321 / 10000) * y * (4 * (1001 / 1000))) * r +
          17321 / 10000 * y * (4 * (1001 / 1000)) + 17321 / 10000 * y * 2 := by gcongr
      _ ≤ 107 / 10 * y := by nlinarith

/-- `cA0 ≤ 0.55/√n`. -/
theorem cA0_le : cA0 n (mA n) ≤ 55 / 100 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb2 := bG_nonneg hG
  have hb3 := bG_nonneg hGk
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b2 := b2_le
  have g2 := g2_le
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have h2 := sqrt2_le
  have hK := Kr_mA_le hn
  have hK0 := Kr_nonneg (mA n)
  have hK4 := K4_le hn
  have hK40 := K4_nonneg n
  have a1 := nc0_le hn
  have a2 := SS_le hn
  have a3 := DS_le hn
  have a4 := LS_le hn
  have a5 := sS_le hn
  have a6 := dS_le hn
  have a7 := lS_le hn
  have n1 := nc0_nn (mA n)
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := sS_nn (mA n)
  have n6 := dS_nn (mA n)
  have n7 := lS_nn (mA n)
  rw [← hy] at a1 a3 a4 a6 a7
  have hyr : y * r ≤ y * (1 / 90) := mul_le_mul_of_nonneg_left hr2 hy0.le
  have hzy : z * y ≤ y * (1 / 64) := by nlinarith
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
  have hyz' : y ≤ z * (1 / 64) := by nlinarith
  rw [cA0_eq, sqrt_mA, mA_eqR]
  refine le_trans (le_of_eq (?_ : _ =
    2 * nc0 (mA n) * r + bG (kappa ∘ kappa) * SS (mA n) * r +
      (kappa ∘ kappa) 0 * (K4 n * y * SS (mA n) + √2 * z * DS (mA n) + 2 * LS (mA n)) +
      (bG (kappa ∘ kappa) * (√5 * (y / 2)) * sS (mA n) +
        (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n) +
          2 * lS (mA n))) +
      (bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
        ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)))) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 55 / 100 * z) (le_of_eq (by rw [hz]; ring))
    calc 2 * nc0 (mA n) * r + bG (kappa ∘ kappa) * SS (mA n) * r +
          (kappa ∘ kappa) 0 * (K4 n * y * SS (mA n) + √2 * z * DS (mA n) + 2 * LS (mA n)) +
          (bG (kappa ∘ kappa) * (√5 * (y / 2)) * sS (mA n) +
            (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n) +
              2 * lS (mA n))) +
          (bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
            ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))
        ≤ 2 * (815 / 1000 * y) * r + 33087 / 100000 * (2005 / 1000) * r +
          49376 / 100000 * (3466 / 1000 * y * (2005 / 1000) +
            141422 / 100000 * z * (895 / 100 * y) + 2 * (12 / 1000 * y)) +
          (33087 / 100000 * (223607 / 100000 * (y / 2)) * (2002 / 1000) +
            49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (2002 / 1000) +
              223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2))) +
          (28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
            1 * (4 * (11 / 5) * y ^ 2 * 2)) := by gcongr
      _ ≤ 55 / 100 * z := by nlinarith

/-- `dA1 ≤ 4097/4096`. -/
theorem dA1_le : dA1 n (mA n) ≤ 4097 / 4096 := by
  unfold dA1
  calc √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 4096 := sqrt_one_add_le hn
    _ = 4097 / 4096 := by norm_num

/-- `dA0 ≤ 0.82/n`. -/
theorem dA0_le : dA0 n (mA n) ≤ 82 / 100 / (n : ℝ) := by
  have h1 := sqrt_one_add_le hn
  have a1 := nc0_le hn
  have n1 := nc0_nn (mA n)
  have hy0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold dA0
  refine le_trans (?_ : _ ≤ 82 / 100 * (1 / (n : ℝ))) (le_of_eq (by ring))
  calc √(1 + 2 / (n : ℝ)) * nc0 (mA n) ≤ (1 + 1 / 4096) * (815 / 1000 * (1 / (n : ℝ))) := by
        gcongr
    _ ≤ 82 / 100 * (1 / (n : ℝ)) := by nlinarith

/-- `dA2 ≤ 10.5/n`. -/
theorem dA2_le : dA2 n (mA n) ≤ 105 / 10 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h1 := sqrt_one_add_le hn
  have h3 := sqrt3_le
  have hQ := Q2_le hn
  unfold dA2
  rw [sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))))) ?_
  · rw [hy]; ring
  · refine le_trans (?_ : _ ≤ 105 / 10 * y) (le_of_eq (by rw [hy]; ring))
    calc √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))
        ≤ (1 + 1 / 4096) * (2 * (17321 / 10000) * y + 17321 / 10000 * y *
          (4 * (1001 / 1000))) := by gcongr
      _ ≤ 105 / 10 * y := by nlinarith

/-- `cAdlt ≤ 7.2/n`. -/
theorem cAdlt_le : cAdlt n (mA n) ≤ 72 / 10 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h2 := sqrt2_le
  have hK4 := K4_le hn
  have hK40 := K4_nonneg n
  have a2 := SS_le hn
  have a3 := DS_le hn
  have a4 := LS_le hn
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  rw [← hy] at a3 a4
  have hzy : z * y ≤ y * (1 / 64) := by nlinarith
  unfold cAdlt
  refine le_trans (le_of_eq (?_ : _ = LS (mA n) + K4 n * y * SS (mA n) +
    √2 * z * DS (mA n))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 72 / 10 * y) (le_of_eq (by rw [hy]; ring))
    calc LS (mA n) + K4 n * y * SS (mA n) + √2 * z * DS (mA n)
        ≤ 12 / 1000 * y + 3466 / 1000 * y * (2005 / 1000) +
          141422 / 100000 * z * (895 / 100 * y) := by gcongr
      _ ≤ 72 / 10 * y := by nlinarith

end focusBounds

end BstLean.Part142

open BstLean.Part142 in
#print axioms agent_phi_L2_of
open BstLean.Part142 in
#print axioms agent_diff_L2_of
open BstLean.Part142 in
#print axioms agent_dlt_L2_of
open BstLean.Part142 in
#print axioms cA0_le
open BstLean.Part142 in
#print axioms cA1_le
open BstLean.Part142 in
#print axioms cA2_le
open BstLean.Part142 in
#print axioms dA0_le
open BstLean.Part142 in
#print axioms dA1_le
open BstLean.Part142 in
#print axioms dA2_le
open BstLean.Part142 in
#print axioms cAdlt_le
