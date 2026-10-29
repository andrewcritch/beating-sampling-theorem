import BstLean.Part141Tau

/-!
# Part 141, item 3: the error of the mean over the cheap stand-in with the ARITHMETIC centre and
the ARITHMETIC scalar

Role: `delegations/statements/p141-spec.md`, item 3. The route is a perturbation from Part 140:
the estimate `ĝ = gHat` of Part 140 (centre `b̂ = ψ_s(M₂h̄₁)`, scalar `τ̂₀`) is compared with the
estimate `g̃ = gA` (centre `b̃ = bA`, scalar `τ̃₀ = tauA`: a finite ReLU sum and rational
constants only) by two Hellinger steps: a change of scale (`gaussScale138_sph`, Part 138) and a
change of centre (`cheapShift141`).

* `cenA W = M₃ b̃`, `tauWA W = τ̃₀`, **`gA W A F = E F(A(x))`, `x = sphPt(M₃ b̃ + τ̃₀γ)`**.
* `diff_pt`: for one `(A, F)` and one `M₃`: `(g̃ − ĝ)² ≤ |c̃ − ĉ|²/τ̃₀²·(I₁ + I₂) +
  4·hellG n τ̃₀ τ̂₀·(I₂ + I₃)`, `I_j` second moments of `F∘A`.
* `diffFixedA`: for fixed `(M₁, M₂) ∈ goodA n`: `E_{M₃} E_{A,F} (g̃ − ĝ)² ≤
  n·(404·t|b̃ − b̂|²/γ + 29/q²)·(4/n)`.
* **`diffVecA_lint`**: `E_{W,A,F}[1_good·(g̃ − ĝ)²] ≤ pertA n·(4/n)`, `pertA n = 27501·n/q²`
  (`q = qA n = 10000·n`, so `pertA n = 27501/(10⁸·n)`).
* **`errVecA_lint`**, `errVecA`, `errTailA`: `E_{W,A,F}[1_good·(g̃ − B)²] ≤
  ((1 + η′)·((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ) + (1 + 1/η′)·pertA n)·(4/n)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-! ## The estimate with the arithmetic centre and scalar -/

section defs

variable {n mA mF : ℕ}

/-- `c̃ = M₃ b̃`: the centre of the cheap stand-in of the arithmetic program. -/
noncomputable def cenA (W : MlpParam (2 * n) (mW n) n) : Fin n → ℝ :=
  W.2.2.mulVec (bA n (W.1, W.2.1))

/-- `τ̃₀` as a function of `W`. -/
noncomputable def tauWA (W : MlpParam (2 * n) (mW n) n) : ℝ := tauA n (W.1, W.2.1)

/-- **The estimate of the arithmetic program with an exact mean** `g̃(W, A, F) = E F(A(x))`,
`x = sphPt(M₃ b̃ + τ̃₀γ)`, `γ` a standard Gaussian vector of `ℝⁿ`. -/
noncomputable def gA (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : ℝ :=
  ∫ x, phiN A F x ∂cheapIn (cenA W) (tauWA W)

lemma measurable_cenA : Measurable (cenA : MlpParam (2 * n) (mW n) n → Fin n → ℝ) := by
  have hθ : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ((W.1, W.2.1) : HidParam (2 * n) (mW n))) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  exact measurable_mulVec_joint.comp
    ((measurable_snd.comp measurable_snd).prodMk ((measurable_bA n).comp hθ))

lemma measurable_tauWA : Measurable (tauWA : MlpParam (2 * n) (mW n) n → ℝ) := by
  have hθ : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ((W.1, W.2.1) : HidParam (2 * n) (mW n))) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  exact (measurable_tauA n).comp hθ

/-- `g̃` is jointly measurable in `(W, A, F)`. -/
lemma measurable_gA :
    Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n mA n × MlpParam n mF 1 =>
      gA t.1 t.2.1 t.2.2) := by
  have hc := measurable_cenA (n := n)
  have hτ := measurable_tauWA (n := n)
  have hW : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n mA n ×
      MlpParam n mF 1) × (Fin n → ℝ) => q.1.1) := measurable_fst.comp measurable_fst
  have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n mA n ×
      MlpParam n mF 1) × (Fin n → ℝ) => phiN q.1.2.1 q.1.2.2
        (sphPt (cenA q.1.1 + tauWA q.1.1 • q.2))) :=
    BstLean.Part131.continuous_phiN_all.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_sphPt.comp ((hc.comp hW).add ((hτ.comp hW).smul measurable_snd))))
  have e : (fun t : MlpParam (2 * n) (mW n) n × MlpParam n mA n × MlpParam n mF 1 =>
      gA t.1 t.2.1 t.2.2) = fun t => ∫ γ, phiN t.2.1 t.2.2
        (sphPt (cenA t.1 + tauWA t.1 • γ)) ∂stdGauss (Fin n) := by
    funext t
    unfold gA
    exact integral_cheapIn _ _ (continuous_phiN _ _).measurable
  rw [e]
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

/-- The second moment of `F∘A` under a cheap stand-in, as an integral over `γ`. -/
lemma sqInt_cheapIn (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) :
    ENNReal.ofReal (∫ x, phiS A F x ^ 2 ∂cheapIn c τ) =
      Lout (stdGauss (Fin n)) (fun γ : Fin n → ℝ => c + τ • γ) (A, F) := by
  have ho : Measurable (fun γ : Fin n → ℝ => c + τ • γ) :=
    measurable_const.add (measurable_const_smul τ)
  rw [← ofReal_integral_out (stdGauss (Fin n)) hn A F ho,
    integral_cheapIn c τ ((bm_phiS hn A F).meas.pow_const 2)]
  simp only [phiS, sphPt_idem hn]

/-- **Two Hellinger steps, for one `(A, F)`**: a change of centre at the scale `a`, then a change
of scale at the centre `c`. -/
lemma diff_pt (hn : 1 ≤ n) (c c' : Fin n → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    (∫ x, phiN A F x ∂cheapIn c' a - ∫ x, phiN A F x ∂cheapIn c b) ^ 2 ≤
      normSq (c' - c) / a ^ 2 *
          (∫ x, phiS A F x ^ 2 ∂cheapIn c' a + ∫ x, phiS A F x ^ 2 ∂cheapIn c a) +
        4 * hellG n a b *
          (∫ x, phiS A F x ^ 2 ∂cheapIn c a + ∫ x, phiS A F x ^ 2 ∂cheapIn c b) := by
  have hφ : BM (phiS A F) := bm_phiS hn A F
  rw [← integral_phiS_cheapIn hn, ← integral_phiS_cheapIn hn]
  have h1 := cheapShift141 c c' ha hφ
  have h2 := gaussScale138_sph hn c ha.le hb hφ
  set x := ∫ x, phiS A F x ∂cheapIn c' a
  set y := ∫ x, phiS A F x ∂cheapIn c a
  set z := ∫ x, phiS A F x ∂cheapIn c b
  set I1 := ∫ x, phiS A F x ^ 2 ∂cheapIn c' a
  set I2 := ∫ x, phiS A F x ^ 2 ∂cheapIn c a
  set I3 := ∫ x, phiS A F x ^ 2 ∂cheapIn c b
  have h3 : (x - z) ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * (y - z) ^ 2 := by
    nlinarith [sq_nonneg (x - 2 * y + z)]
  have e : 2 * (normSq (c' - c) / (2 * a ^ 2) * (I1 + I2)) =
      normSq (c' - c) / a ^ 2 * (I1 + I2) := by
    field_simp
  linarith

end defs

/-! ## Fixed `(M₁, M₂)` -/

section fixed

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodA n)

include hn hθ

/-- For fixed `(M₁, M₂) ∈ goodA n` and fixed `M₃`: the mean over `(A, F)` of `(g̃ − ĝ)²`. -/
lemma diffFixedM (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal ((2 * (normSq (M₃.mulVec (bA n θ - bhat θ)) / tauA n θ ^ 2) +
      8 * hellG n (tauA n θ) (tauHat (2 * n) (mW n) θ)) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have ha := tauA_pos hn hθ
  have hb := tauHat_pos hn hθ.1
  set a : ℝ := tauA n θ with had
  set b : ℝ := tauHat (2 * n) (mW n) θ with hbd
  set c : Fin n → ℝ := M₃.mulVec (bhat θ) with hc
  set c' : Fin n → ℝ := M₃.mulVec (bA n θ) with hc'
  have hcc : c' - c = M₃.mulVec (bA n θ - bhat θ) := by
    rw [hc, hc', Matrix.mulVec_sub]
  set w : ℝ := normSq (c' - c) / a ^ 2 with hw
  have hw0 : 0 ≤ w := div_nonneg (normSq_nonneg _) (sq_nonneg _)
  set H : ℝ := 4 * hellG n a b with hH
  have hH0 : 0 ≤ H := mul_nonneg (by norm_num) (hellG_nonneg _ _ _)
  set o1 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c' + a • γ with ho1
  set o2 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c + a • γ with ho2
  set o3 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c + b • γ with ho3
  have mo1 : Measurable o1 := measurable_const.add (measurable_const_smul a)
  have mo2 : Measurable o2 := measurable_const.add (measurable_const_smul a)
  have mo3 : Measurable o3 := measurable_const.add (measurable_const_smul b)
  set P := stdGauss (Fin n) with hP
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2) ≤
      ENNReal.ofReal w * (Lout P o1 p + Lout P o2 p) +
        ENNReal.ofReal H * (Lout P o2 p + Lout P o3 p) := by
    rintro ⟨A, F⟩
    have h := diff_pt hn1 c c' ha hb A F
    have i1 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c' a := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c a := integral_nonneg fun _ => sq_nonneg _
    have i3 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c b := integral_nonneg fun _ => sq_nonneg _
    rw [← sqInt_cheapIn hn1 c' a A F, ← sqInt_cheapIn hn1 c a A F, ← sqInt_cheapIn hn1 c b A F,
      ← ENNReal.ofReal_add i1 i2, ← ENNReal.ofReal_add i2 i3,
      ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hH0,
      ← ENNReal.ofReal_add (mul_nonneg hw0 (add_nonneg i1 i2))
        (mul_nonneg hH0 (add_nonneg i2 i3))]
    refine ENNReal.ofReal_le_ofReal ?_
    exact h
  refine (lintegral_mono key).trans (le_of_eq ?_)
  have m1 := measurable_Lout (mA := mA n) (mF := mF n) P mo1
  have m2 := measurable_Lout (mA := mA n) (mF := mF n) P mo2
  have m3 := measurable_Lout (mA := mA n) (mF := mF n) P mo3
  have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  have m12 : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P o1 p + Lout P o2 p) := m1.add m2
  have m23 : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P o2 p + Lout P o3 p) := m2.add m3
  have hA : ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, (Lout P o1 p + Lout P o2 p)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [lintegral_add_left m1, lintegral_Lout P hn1 hmA hmF mo1,
      lintegral_Lout P hn1 hmA hmF mo2]
  have hB : ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, (Lout P o2 p + Lout P o3 p)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [lintegral_add_left m2, lintegral_Lout P hn1 hmA hmF mo2,
      lintegral_Lout P hn1 hmA hmF mo3]
  rw [lintegral_add_left (m12.const_mul (ENNReal.ofReal w)), lintegral_const_mul _ m12,
    lintegral_const_mul _ m23, hA, hB]
  rw [← ENNReal.ofReal_add h4 h4, ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hH0,
    ← ENNReal.ofReal_add (mul_nonneg hw0 (add_nonneg h4 h4))
      (mul_nonneg hH0 (add_nonneg h4 h4))]
  congr 1
  rw [hw, hH, hcc]
  ring

/-- **For fixed `(M₁, M₂) ∈ goodA n`**: `E_{M₃} E_{A,F} (g̃ − ĝ)² ≤
`n·(404·t|b̃ − b̂|²/γ + 29/q²)·(4/n)`. -/
theorem diffFixedA :
    ∫⁻ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
        ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2)
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
      ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
    ENNReal.ofReal ((n : ℝ) * (404 * (dA n θ / (2 / ((2 * n : ℕ) : ℝ))) +
      29 * (1 / (qA n : ℝ)) ^ 2) * (4 / (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have ha := tauA_pos hn hθ
  set a : ℝ := tauA n θ with had
  set Hh : ℝ := hellG n a (tauHat (2 * n) (mW n) θ) with hHh
  have hH0 : 0 ≤ Hh := hellG_nonneg _ _ _
  set d : Fin (mW n) → ℝ := bA n θ - bhat θ with hd
  obtain ⟨li, le⟩ := layer_sq (m := n) (k := mW n) (v := 2 / (mW n : ℝ)) (by positivity) d
  set f : Matrix (Fin n) (Fin (mW n)) ℝ → ℝ := fun M₃ =>
    (2 * (normSq (M₃.mulVec d) / a ^ 2) + 8 * Hh) * (4 / (n : ℝ)) with hf
  have hf0 : ∀ M₃, 0 ≤ f M₃ := fun M₃ => by
    have : 0 ≤ normSq (M₃.mulVec d) / a ^ 2 := div_nonneg (normSq_nonneg _) (sq_nonneg _)
    rw [hf]; positivity
  have hfi : Integrable f (gaussMat n (mW n) (2 / (mW n : ℝ))) := by
    rw [hf]
    exact ((((li.div_const _).const_mul 2).add (integrable_const _)).mul_const _)
  have hfint : ∫ M₃, f M₃ ∂gaussMat n (mW n) (2 / (mW n : ℝ)) =
      (8 * Hh + 2 * (n : ℝ) * dA n θ / a ^ 2) * (4 / (n : ℝ)) := by
    rw [hf, integral_mul_const, integral_add ((li.div_const _).const_mul 2)
      (integrable_const _), integral_const_mul, integral_div, le]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    unfold dA
    rw [← hd]
    ring
  calc _ ≤ ∫⁻ M₃, ENNReal.ofReal (f M₃) ∂gaussMat n (mW n) (2 / (mW n : ℝ)) :=
        lintegral_mono fun M₃ => diffFixedM hn hθ M₃
    _ = ENNReal.ofReal (∫ M₃, f M₃ ∂gaussMat n (mW n) (2 / (mW n : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)).symm
    _ ≤ _ := by
        rw [hfint]
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (KA_le hn hθ) (by positivity)

end fixed

/-! ## Joint over `(W, A, F)` -/

/-- The good hidden event `goodA n` as an event of the whole World network. -/
def goodWA (n : ℕ) : Set (MlpParam (2 * n) (mW n) n) := {W | (W.1, W.2.1) ∈ goodA n}

lemma goodWA_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (goodWA n) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (goodA_meas hn)

lemma goodWA_sub (n : ℕ) : goodWA n ⊆ goodWH n := fun _ hW => hW.1

/-- The price of the perturbation: `pertA n = 27501·n/(qA n)²`. -/
noncomputable def pertA (n : ℕ) : ℝ := 27501 * (n : ℝ) / (qA n : ℝ) ^ 2

lemma pertA_nonneg (n : ℕ) : 0 ≤ pertA n := by unfold pertA; positivity

/-- `1_good(W)·(g̃ − ĝ)²`, a function of `(W, A, F)`. -/
noncomputable def dGA (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodWA n).indicator (fun W => (gA W t.2.1 t.2.2 - gHat W t.2.1 t.2.2) ^ 2) t.1

/-- `1_good(W)·(g̃ − B)²`, a function of `(W, A, F)`. -/
noncomputable def errGA (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodWA n).indicator (fun W => (gA W t.2.1 t.2.2 - Part130.Bn W t.2.1 t.2.2) ^ 2) t.1

lemma dGA_nonneg (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ dGA n t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma errGA_nonneg (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ errGA n t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma ind_fst_eq {α β : Type*} (G : Set α) (h : α → β → ℝ) (t : α × β) :
    G.indicator (fun W => h W t.2) t.1 =
      ({t | t.1 ∈ G} : Set (α × β)).indicator (fun t => h t.1 t.2) t := by
  by_cases ht : t.1 ∈ G
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ {t : α × β | t.1 ∈ G} from ht)]
  · rw [Set.indicator_of_notMem ht,
      Set.indicator_of_notMem (show t ∉ {t : α × β | t.1 ∈ G} from ht)]

lemma measurable_dGA {n : ℕ} (hn : 1 ≤ n) : Measurable (dGA n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : dGA n = ({t | t.1 ∈ goodWA n} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gA t.1 t.2.1 t.2.2 - gHat t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    exact ind_fst_eq (goodWA n) (fun W p => (gA W p.1 p.2 - gHat W p.1 p.2) ^ 2) t
  rw [e]
  exact ((measurable_gA.sub (measurable_gHat hN)).pow_const 2).indicator
    (measurable_fst (goodWA_meas hn))

lemma measurable_errGA {n : ℕ} (hn : 1 ≤ n) : Measurable (errGA n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errGA n = ({t | t.1 ∈ goodWA n} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    exact ind_fst_eq (goodWA n) (fun W p => (gA W p.1 p.2 - Part130.Bn W p.1 p.2) ^ 2) t
  rw [e]
  exact ((measurable_gA.sub (BstLean.Part131.measurable_Bn hN)).pow_const 2).indicator
    (measurable_fst (goodWA_meas hn))

/-- **The distance of the two estimates, joint over `(W, A, F)`.** For `n ≥ 4096`:
`E_{W,A,F}[1_good(W)·(g̃ − ĝ)²] ≤ pertA n·(4/n)`. -/
theorem diffVecA_lint {n : ℕ} (hn : 4096 ≤ n) :
    ∫⁻ t, ENNReal.ofReal (dGA n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (pertA n * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have mE := goodA_meas (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (dGA n t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_dGA hn1)
  set G : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hG
  have mG : Measurable G := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, G W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mG MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => G (MeasurableEquiv.prodAssoc a))
      (mG.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    (n : ℝ) * (404 * (dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) *
      (4 / (n : ℝ)) with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have := dA_nonneg n θ
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    by_cases hθ : θ ∈ goodA n
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWA n := fun M₃ => hθ
      have hin : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, G (θ.1, θ.2, M₃) =
          ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
            ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2) ∂PAF := by
        intro M₃
        refine lintegral_congr fun p => ?_
        simp only [hf, dGA, Set.indicator_of_mem (hW M₃)]
      simp_rw [hin]
      exact diffFixedA hn hθ
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWA n := fun M₃ => hθ
      have hz : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, G (θ.1, θ.2, M₃) = 0 := by
        intro M₃
        simp only [hG, hf, dGA, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero,
          lintegral_zero]
      simp_rw [hz]
      simp
  obtain ⟨hdi, hdb⟩ := centreArith141 hn
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := by
    rw [hk]
    exact ((((hdi.div_const _).const_mul 404).add (integrable_const _)).const_mul _).mul_const _
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_mul_const, integral_const_mul,
          integral_add ((hdi.div_const _).const_mul 404) (integrable_const _),
          integral_const_mul, integral_div]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        have h1 : (∫ θ, dA n θ ∂hidGauss (2 * n) (mW n)) / (2 / ((2 * n : ℕ) : ℝ)) ≤
            68 / (qA n : ℝ) ^ 2 := by
          rw [div_le_iff₀ hγ]
          linarith
        have h2 : (n : ℝ) * (404 * ((∫ θ, dA n θ ∂hidGauss (2 * n) (mW n)) /
            (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) ≤ pertA n := by
          unfold pertA
          have e1 : 27501 * (n : ℝ) / (qA n : ℝ) ^ 2 =
              (n : ℝ) * (404 * (68 / (qA n : ℝ) ^ 2) + 29 * (1 / (qA n : ℝ)) ^ 2) := by
            field_simp
            ring
          rw [e1]
          exact mul_le_mul_of_nonneg_left (by linarith) hnpos.le
        exact mul_le_mul_of_nonneg_right h2 (by positivity)

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)
  {η' : ℝ} (hη' : 0 < η')

include hn hζ0 hζ1 hη hη'

/-- **The error of the arithmetic estimate, joint over `(W, A, F)`.** -/
theorem errVecA_lint :
    ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) +
        4 * (1 + 1 / η) * EHH n ζ) + (1 + 1 / η') * pertA n) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (errGH n t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
  have m2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dGA n t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dGA hn1)
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (errGA n t) ≤
        ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGH n t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGA n t) := by
    intro t
    have h0 := errGH_nonneg n t
    have h0' := dGA_nonneg n t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : t.1 ∈ goodWA n
    · have ht' : t.1 ∈ goodWH n := goodWA_sub n ht
      simp only [errGA, errGH, dGA, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      have hs := sq_split (η := 1 / η') (by positivity) (gA t.1 t.2.1 t.2.2)
        (gHat t.1 t.2.1 t.2.2) (Part130.Bn t.1 t.2.1 t.2.2)
      rw [one_div_one_div] at hs
      linarith
    · simp only [errGA, Set.indicator_of_notMem ht]
      positivity
  calc ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGH n t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGA n t)) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ENNReal.ofReal (1 + η') * ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n +
          ENNReal.ofReal (1 + 1 / η') * ∫⁻ t, ENNReal.ofReal (dGA n t) ∂mlpTriple 2 n := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η') * ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) +
            4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (pertA n * (4 / (n : ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (errVecHat_lint hn hζ0 hζ1 hη))
          (mul_le_mul' le_rfl (diffVecA_lint hn))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The same as an integral. -/
theorem errVecA :
    Integrable (errGA n) (mlpTriple 2 n) ∧
      ∫ t, errGA n t ∂mlpTriple 2 n ≤ ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) +
        4 * (1 + 1 / η) * EHH n ζ) + (1 + 1 / η') * pertA n) * (4 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := errVecA_lint hn hζ0 hζ1 hη hη'
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have hc : (0 : ℝ) ≤ ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) +
      4 * (1 + 1 / η) * EHH n ζ) + (1 + 1 / η') * pertA n) * (4 / (n : ℝ)) := by positivity
  have h0 : 0 ≤ᵐ[mlpTriple 2 n] errGA n := Filter.Eventually.of_forall (errGA_nonneg n)
  have hm := (measurable_errGA hn1).aestronglyMeasurable (μ := mlpTriple 2 n)
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
  exact ENNReal.toReal_le_of_le_ofReal hc h

/-- The tail form: for `s > 0`: `Pr(W good and (g̃ − B)² ≥ s) ≤ (the bound)/s`. -/
theorem errTailA {s : ℝ} (hs : 0 < s) :
    (mlpTriple 2 n).real {t | s ≤ errGA n t} ≤
      ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
        (1 + 1 / η') * pertA n) * (4 / (n : ℝ)) / s := by
  obtain ⟨hi, hb⟩ := errVecA hn hζ0 hζ1 hη hη'
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := mlpTriple 2 n) (f := errGA n)
    (Filter.Eventually.of_forall (errGA_nonneg n)) hi s
  rw [le_div_iff₀ hs]
  linarith

end joint

end BstLean.Part141

open BstLean.Part141 in
#print axioms diffFixedA
open BstLean.Part141 in
#print axioms diffVecA_lint
open BstLean.Part141 in
#print axioms errVecA_lint
open BstLean.Part141 in
#print axioms errVecA
open BstLean.Part141 in
#print axioms errTailA
