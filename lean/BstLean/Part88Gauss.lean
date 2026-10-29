import BstLean.Part88Defs
import BstLean.Part84Gauss

/-!
# Part 88, the Gaussian model on a scale window (`gaussModel88`)

Assembly of `GM88` from the interfaces of `Part84Defs` and `Part88Defs`. The proof adapts
`Part84.gaussModel`: one level `L = en k (eD d) A` for every scale of the window, the centre
`Vb lam = ∫ en + ∫ (hmean − g)² − ∫ errW²`, and a drift bound for the centre.
-/

namespace BstLean.Part88

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (frob IsSymmT Tens varU)
open BstLean.Part53 (heatA tinner p4)
open BstLean.Part81 (JJ WIdx pf kap eD)
open BstLean.Part84

variable {n d k : ℕ}

/-- The variance constant with a weight `ϑ` between the two parts of `V = X − err²`. -/
noncomputable def cVX (n d k : ℕ) (CF K4 KX τ ϑ : ℝ) : ℝ :=
  (1 + ϑ) * KX * ((1 + τ) ^ (2 * k) + (τ / k) ^ 2 * (1 + τ) ^ k) ^ 2 +
    (1 + 1 / ϑ) * K4 * c1G n d k CF τ ^ 2 / n

/-- The hypothesis on the variance of `X = E_x (F_x − g₀)²` over `W`, with the constant `KX`:
`Var_W X ≤ (KX/n) E_x (E_W (F_x − g₀)²)²`. -/
def XVar (n d k : ℕ) (w KX : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ k → ∀ A : Tens n, Rep84 n d k P A →
    ∀ lam : ℝ, |lam ^ 2 - 1| ≤ w / (n : ℝ) →
    ∫ W : WIdx n d → ℝ, (BW ((P - MvPolynomial.C (g0P d P)) ^ 2) lam W -
        ∫ W' : WIdx n d → ℝ, BW ((P - MvPolynomial.C (g0P d P)) ^ 2) lam W'
          ∂stdGauss (WIdx n d)) ^ 2 ∂stdGauss (WIdx n d) ≤
      KX / n * ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
        (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2) ^ 2 ∂uniformSphere n

lemma sq_sub_le_theta (a b ϑ : ℝ) (hϑ : 0 < ϑ) :
    (a - b) ^ 2 ≤ (1 + ϑ) * a ^ 2 + (1 + 1 / ϑ) * b ^ 2 := by
  have h : 0 ≤ (ϑ * a + b) ^ 2 / ϑ := by positivity
  have e : (ϑ * a + b) ^ 2 / ϑ = ϑ * a ^ 2 + 2 * a * b + 1 / ϑ * b ^ 2 := by
    field_simp; ring
  rw [e] at h
  nlinarith

lemma cont_tau (n d k : ℕ) (w : ℝ) :
    Continuous (fun x : Fin n → ℝ => tauF n d k w (n * p4 x)) := by
  unfold tauF p4
  fun_prop

/-- Pointwise bounds on the sphere. -/
lemma ptwise88 (hd : 1 ≤ d) (hk : 1 ≤ k) (w : ℝ) (hw0 : 0 ≤ w) (hw : w / (n : ℝ) ≤ 1 / 10)
    (hSc : ScaleIface n k) (hPt : PtIface88 n d k w) (A : Tens n) (hA : ∀ j, IsSymmT (A j))
    (lam : ℝ) (hlam : |lam ^ 2 - 1| ≤ w / (n : ℝ)) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    0 ≤ tauF n d k w (n * p4 x) ∧
    (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2 ≤
      (tauF n d k w (n * p4 x) / k) ^ 2 * (1 + tauF n d k w (n * p4 x)) ^ k * en k (eD d) A ∧
    en k (lam ^ 2 * kap d x x) A ≤ (1 + tauF n d k w (n * p4 x)) ^ (2 * k) * en k (eD d) A ∧
    (1 - 2 * k * (tauF n d k w (n * p4 x))) * en k (eD d) A ≤ en k (lam ^ 2 * kap d x x) A ∧
    0 ≤ en k (lam ^ 2 * kap d x x) A ∧
    (en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2
      ≤ ((1 + tauF n d k w (n * p4 x)) ^ (2 * k) +
          (tauF n d k w (n * p4 x) / k) ^ 2 * (1 + tauF n d k w (n * p4 x)) ^ k) ^ 2 *
        en k (eD d) A ^ 2 := by
  obtain ⟨hs9, hse⟩ := hPt lam hlam x hx
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have hwn : 0 ≤ w / (n : ℝ) := by positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = eD d * (1 - w / n) := ⟨_, rfl⟩
  have hs0pos : 0 < s0 := by rw [hs0]; exact mul_pos (by linarith) (by linarith)
  have hs0le : s0 ≤ eD d := by rw [hs0]; nlinarith
  rw [← hs0] at hs9 hse
  have hE : 0 ≤ en k (eD d) A := en_nonneg _ (by linarith) A
  have hv : 0 ≤ en k (lam ^ 2 * kap d x x) A := en_nonneg _ (by linarith) A
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = tauF n d k w (n * p4 x) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = lam ^ 2 * kap d x x := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = en k (eD d) A := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = en k s A := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = (hmean k s A - hmean k (eD d) A) ^ 2 := ⟨_, rfl⟩
  rw [← hy, ← hs, ← hEd, ← hvd, ← hqd]
  rw [← hy, ← hs] at hse
  rw [← hs] at hs9 hv
  rw [← hEd] at hE
  rw [← hvd] at hv
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = |s - eD d| * Real.sqrt n / s0 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by positivity) hs0pos.le
  have hkt : (k : ℝ) * t ≤ y := by rw [ht]; exact hse
  have hy0 : 0 ≤ y := le_trans (mul_nonneg hk0.le ht0) hkt
  have htk : t ≤ y / k := by rw [le_div_iff₀ hk0]; linarith
  have hkt0 : (0 : ℝ) ≤ 1 + k * t := by positivity
  have hle : 1 + (k : ℝ) * t ≤ 1 + y := by linarith
  obtain ⟨h1, h2⟩ := hSc A hA (eD d) s s0 hs0pos hs0le hs9
  obtain ⟨-, h3⟩ := hSc A hA s (eD d) s0 hs0pos hs9 hs0le
  rw [abs_sub_comm] at h3
  rw [← ht, ← hEd] at h1 h2
  rw [← ht, ← hEd, ← hvd] at h3
  rw [← hqd] at h1
  rw [← hvd] at h2
  have R1 : q ≤ (y / k) ^ 2 * (1 + y) ^ k * E :=
    h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ ht0 htk 2) (pow_le_pow_left₀ hkt0 hle k)
        (pow_nonneg hkt0 k) (sq_nonneg _)) hE)
  have R2 : v ≤ (1 + y) ^ (2 * k) * E :=
    h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkt0 hle _) hE)
  have R3' : E ≤ (1 + y) ^ (2 * k) * v :=
    h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkt0 hle _) hv)
  have hB := bern84 y hy0 k
  have R3 : (1 - 2 * k * y) * E ≤ v := by
    by_cases hc : 0 ≤ 1 - 2 * k * y
    · calc (1 - 2 * k * y) * E
          ≤ (1 - 2 * k * y) * ((1 + y) ^ (2 * k) * v) :=
            mul_le_mul_of_nonneg_left R3' hc
        _ = ((1 - 2 * k * y) * (1 + y) ^ (2 * k)) * v := by ring
        _ ≤ 1 * v := mul_le_mul_of_nonneg_right hB hv
        _ = v := one_mul _
    · rw [not_le] at hc
      nlinarith
  refine ⟨hy0, R1, R2, R3, hv, ?_⟩
  have hq0 : 0 ≤ q := by rw [hqd]; exact sq_nonneg _
  have hsum : v + q ≤ ((1 + y) ^ (2 * k) + (y / k) ^ 2 * (1 + y) ^ k) * E :=
    calc v + q ≤ (1 + y) ^ (2 * k) * E + (y / k) ^ 2 * (1 + y) ^ k * E := add_le_add R2 R1
      _ = ((1 + y) ^ (2 * k) + (y / k) ^ 2 * (1 + y) ^ k) * E := by ring
  rw [← mul_pow]
  exact pow_le_pow_left₀ (add_nonneg hv hq0) hsum 2

/-- The facts over the sphere. -/
lemma sigmaFacts88 (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 1 ≤ n) (w B : ℝ) (hw0 : 0 ≤ w)
    (hw : w / (n : ℝ) ≤ 1 / 10)
    (hSc : ScaleIface n k) (hPt : PtIface88 n d k w) (hMF : MomFacts88 n d k w B)
    (A : Tens n) (hA : ∀ j, IsSymmT (A j)) (lam : ℝ) (hlam : |lam ^ 2 - 1| ≤ w / (n : ℝ)) :
    Integrable (fun x : Fin n → ℝ => en k (lam ^ 2 * kap d x x) A) (uniformSphere n) ∧
    Integrable (fun x : Fin n → ℝ => hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A)
      (uniformSphere n) ∧
    Integrable (fun x : Fin n → ℝ => (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2)
      (uniformSphere n) ∧
    ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2 ∂uniformSphere n ≤
      (tauF n d k w B / k) ^ 2 * (1 + tauF n d k w B) ^ k * en k (eD d) A ∧
    ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ≤
      (1 + tauF n d k w B) ^ (2 * k) * en k (eD d) A ∧
    (1 - 2 * k * tauF n d k w B) * en k (eD d) A ≤
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ∧
    Integrable (fun x : Fin n → ℝ => (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2) (uniformSphere n) ∧
    ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2 ∂uniformSphere n ≤
      ((1 + tauF n d k w B) ^ (2 * k) + (tauF n d k w B / k) ^ 2 * (1 + tauF n d k w B) ^ k) ^ 2 *
        en k (eD d) A ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hE : 0 ≤ en k (eD d) A :=
    en_nonneg _ (by linarith [BstLean.Part81.one_le_eD d hd]) A
  have hcs : Continuous (fun x : Fin n → ℝ => lam ^ 2 * kap d x x) :=
    continuous_const.mul (BstLean.Part81.cont_kap_diag d)
  have hcv := cont_en (k := k) A _ hcs
  have hcm := (cont_hmean (k := k) A _ hcs).sub
    (continuous_const (y := hmean k (eD d) A))
  have iv := BstLean.Part78.sph_int hn hcv
  have im := BstLean.Part78.sph_int hn hcm
  have iq := BstLean.Part78.sph_int hn (hcm.pow 2)
  have ivq := BstLean.Part78.sph_int hn ((hcv.add (hcm.pow 2)).pow 2)
  have hpt := (BstLean.Part29.uniformSphere_ae_sphere n).mono fun x hx =>
    ptwise88 hd hk w hw0 hw hSc hPt A hA lam hlam x hx
  have hct := cont_tau n d k w
  have hc1 : Continuous (fun x : Fin n → ℝ => 1 + tauF n d k w (n * p4 x)) :=
    continuous_const.add hct
  have iT := BstLean.Part78.sph_int hn hct
  have iB := BstLean.Part78.sph_int hn (hc1.pow (2 * k))
  have iC := BstLean.Part78.sph_int hn (((hct.div_const (k : ℝ)).pow 2).mul (hc1.pow k))
  have iA := BstLean.Part78.sph_int hn
    (((hc1.pow (2 * k)).add (((hct.div_const (k : ℝ)).pow 2).mul (hc1.pow k))).pow 2)
  obtain ⟨m1, m2, m3, m4⟩ := hMF
  -- (b)
  have Hq : ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2
      ∂uniformSphere n ≤
      (tauF n d k w B / k) ^ 2 * (1 + tauF n d k w B) ^ k * en k (eD d) A :=
    calc ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2
          ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, (tauF n d k w (n * p4 x) / k) ^ 2 *
            (1 + tauF n d k w (n * p4 x)) ^ k * en k (eD d) A ∂uniformSphere n :=
          integral_mono_ae iq (iC.mul_const _) (hpt.mono fun x h => h.2.1)
      _ = (∫ x : Fin n → ℝ, (tauF n d k w (n * p4 x) / k) ^ 2 *
            (1 + tauF n d k w (n * p4 x)) ^ k ∂uniformSphere n) * en k (eD d) A :=
          integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right m3 hE
  -- (c)
  have Hv : ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ≤
      (1 + tauF n d k w B) ^ (2 * k) * en k (eD d) A :=
    calc ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, (1 + tauF n d k w (n * p4 x)) ^ (2 * k) * en k (eD d) A
            ∂uniformSphere n :=
          integral_mono_ae iv (iB.mul_const _) (hpt.mono fun x h => h.2.2.1)
      _ = (∫ x : Fin n → ℝ, (1 + tauF n d k w (n * p4 x)) ^ (2 * k) ∂uniformSphere n) *
            en k (eD d) A := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right m2 hE
  -- (d)
  have Hfl : (1 - 2 * k * tauF n d k w B) * en k (eD d) A ≤
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n := by
    have il0 : Integrable (fun x : Fin n → ℝ => 1 - 2 * (k : ℝ) * (tauF n d k w (n * p4 x)))
        (uniformSphere n) := (integrable_const (1 : ℝ)).sub (iT.const_mul _)
    have e0 : ∫ x : Fin n → ℝ, (1 - 2 * (k : ℝ) * (tauF n d k w (n * p4 x))) ∂uniformSphere n =
        1 - 2 * k * ∫ x : Fin n → ℝ, tauF n d k w (n * p4 x) ∂uniformSphere n := by
      have h1 : ∫ x : Fin n → ℝ, (1 - 2 * (k : ℝ) * (tauF n d k w (n * p4 x)))
          ∂uniformSphere n =
          ∫ _x : Fin n → ℝ, (1 : ℝ) ∂uniformSphere n -
            ∫ x : Fin n → ℝ, 2 * (k : ℝ) * (tauF n d k w (n * p4 x)) ∂uniformSphere n :=
        integral_sub (integrable_const (1 : ℝ)) (iT.const_mul _)
      rw [h1, integral_const_mul, integral_const]; simp
    calc (1 - 2 * k * tauF n d k w B) * en k (eD d) A
        ≤ (1 - 2 * k * ∫ x : Fin n → ℝ, tauF n d k w (n * p4 x) ∂uniformSphere n) *
            en k (eD d) A :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [mul_le_mul_of_nonneg_left m1 hk0.le]) hE
      _ = ∫ x : Fin n → ℝ, (1 - 2 * (k : ℝ) * (tauF n d k w (n * p4 x))) * en k (eD d) A
            ∂uniformSphere n := by
          rw [integral_mul_const, e0]
      _ ≤ ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n :=
          integral_mono_ae (il0.mul_const _) iv (hpt.mono fun x h => h.2.2.2.1)
  -- (e)
  have Hvq : ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2 ∂uniformSphere n ≤
      ((1 + tauF n d k w B) ^ (2 * k) + (tauF n d k w B / k) ^ 2 * (1 + tauF n d k w B) ^ k) ^ 2 *
        en k (eD d) A ^ 2 :=
    calc ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
          (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2 ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, ((1 + tauF n d k w (n * p4 x)) ^ (2 * k) +
            (tauF n d k w (n * p4 x) / k) ^ 2 * (1 + tauF n d k w (n * p4 x)) ^ k) ^ 2 *
            en k (eD d) A ^ 2 ∂uniformSphere n :=
          integral_mono_ae ivq (iA.mul_const _) (hpt.mono fun x h => h.2.2.2.2.2)
      _ = (∫ x : Fin n → ℝ, ((1 + tauF n d k w (n * p4 x)) ^ (2 * k) +
            (tauF n d k w (n * p4 x) / k) ^ 2 * (1 + tauF n d k w (n * p4 x)) ^ k) ^ 2
            ∂uniformSphere n) * en k (eD d) A ^ 2 := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right m4 (sq_nonneg _)
  exact ⟨iv, im, iq, Hq, Hv, Hfl, ivq, Hvq⟩

/-- The drift of `∫ en` between two scales of the window. -/
lemma enDrift (hd : 1 ≤ d) (hn : 1 ≤ n) (w : ℝ) (hw0 : 0 ≤ w) (hw : w / (n : ℝ) ≤ 1 / 10)
    (hSc : ScaleIface n k) (hPt : PtIface88 n d k w) (A : Tens n) (hA : ∀ j, IsSymmT (A j))
    (lam lam' : ℝ) (hlam : |lam ^ 2 - 1| ≤ w / (n : ℝ)) (hlam' : |lam' ^ 2 - 1| ≤ w / (n : ℝ)) :
    ∫ x : Fin n → ℝ, en k (lam' ^ 2 * kap d x x) A ∂uniformSphere n ≤
      (1 + k * (|lam' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (lam' ^ 2))) ^ (2 * k) *
        ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have hwn : 0 ≤ w / (n : ℝ) := by positivity
  have hs0pos : 0 < eD d * (1 - w / n) := mul_pos (by linarith) (by linarith)
  have hc : ∀ l : ℝ, Continuous (fun x : Fin n → ℝ => en k (l ^ 2 * kap d x x) A) := fun l =>
    cont_en (k := k) A _ (continuous_const.mul (BstLean.Part81.cont_kap_diag d))
  have iv := BstLean.Part78.sph_int hn (hc lam)
  have iv' := BstLean.Part78.sph_int hn (hc lam')
  rw [← integral_const_mul]
  refine integral_mono_ae iv' (iv.const_mul _) ?_
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  obtain ⟨h1, -⟩ := hPt lam hlam x hx
  obtain ⟨h1', -⟩ := hPt lam' hlam' x hx
  have hκ : 0 < kap d x x := by
    by_contra h
    rw [not_lt] at h
    have := mul_nonneg (sq_nonneg lam) (neg_nonneg.2 h)
    nlinarith
  have h := (hSc A hA (lam ^ 2 * kap d x x) (lam' ^ 2 * kap d x x)
    (min (lam ^ 2 * kap d x x) (lam' ^ 2 * kap d x x))
    (lt_min (by linarith) (by linarith)) (min_le_left _ _) (min_le_right _ _)).2
  have e : |lam' ^ 2 * kap d x x - lam ^ 2 * kap d x x| * Real.sqrt n /
      min (lam ^ 2 * kap d x x) (lam' ^ 2 * kap d x x) =
      |lam' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (lam' ^ 2) := by
    rw [← sub_mul, abs_mul, abs_of_pos hκ, ← min_mul_of_nonneg _ _ hκ.le, mul_right_comm,
      mul_div_mul_right _ _ hκ.ne']
  rw [e] at h
  exact h

/-- The facts at one scale of the window. -/
lemma perLam (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 10 ≤ n) (w B CF K4 KX ϑ : ℝ) (hϑ : 0 < ϑ)
    (hKX : 0 ≤ KX) (hXV : XVar n d k w KX)
    (hw0 : 0 ≤ w) (hw : w / (n : ℝ) ≤ 1 / 10) (hCF : 0 ≤ CF) (hK4 : 0 ≤ K4)
    (hSc : ScaleIface n k) (hDec : DecorIface n d CF) (hFub : FubIface n d)
    (hPt : PtIface88 n d k w) (hMF : MomFacts88 n d k w B) (hPoly : PolyRep n d)
    (h4 : Fourth84 k K4) (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ k) (A : Tens n)
    (hR : Rep84 n d k P A) (lam : ℝ) (hlam : |lam ^ 2 - 1| ≤ w / (n : ℝ)) :
    Integrable (fun W : WIdx n d → ℝ => errW P lam W ^ 2) (stdGauss (WIdx n d)) ∧
    ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2 ∂uniformSphere n ≤
      c1G n d k CF (tauF n d k w B) / n * en k (eD d) A ∧
    ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ≤
      (1 + tauF n d k w B) ^ (2 * k) * en k (eD d) A ∧
    (1 - 2 * k * tauF n d k w B) * en k (eD d) A ≤
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ∧
    ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d) ≤
      c1G n d k CF (tauF n d k w B) / n * en k (eD d) A ∧
    Integrable (fun W : WIdx n d → ℝ => (VW P lam W -
      (∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n +
        ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2 ∂uniformSphere n -
        ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d))) ^ 2)
      (stdGauss (WIdx n d)) ∧
    ∫ W : WIdx n d → ℝ, (VW P lam W -
      (∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n +
        ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2 ∂uniformSphere n -
        ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d))) ^ 2 ∂stdGauss (WIdx n d) ≤
      cVX n d k CF K4 KX (tauF n d k w B) ϑ / n * en k (eD d) A ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn1
  have hA := hR.1
  have hg0 := hR.2.1
  have h3 := hR.2.2.1
  have hS0 := step0 hR lam
  obtain ⟨iv, im, iq, Hq, Hv, Hfl, ivq, Hvq⟩ :=
    sigmaFacts88 hd hk hn1 w B hw0 hw hSc hPt hMF A hA lam hlam
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have he0 : 0 < eD d := by linarith
  have hE : 0 ≤ en k (eD d) A := en_nonneg _ (by linarith) A
  rw [← hg0] at im iq Hq ivq Hvq
  have herrdef : ∀ W : WIdx n d → ℝ, errW P lam W = BW P lam W - g0P d P := fun W => rfl
  have hXV0 := hXV P hP A hR lam hlam
  clear hg0 hR hMF
  generalize tauF n d k w B = T at *
  have hpe : 0 ≤ (1 + T) ^ (2 * k) := by rw [pow_mul]; positivity
  have hc1e : ∀ E : ℝ, c1G n d k CF T / n * E =
      (T / k) ^ 2 * (1 + T) ^ k * E + CF / (eD d * n) * ((1 + T) ^ (2 * k) * E) := by
    intro E; unfold c1G; field_simp
  have hcVe : ∀ E : ℝ, (1 + ϑ) * (KX / n *
      (((1 + T) ^ (2 * k) + (T / k) ^ 2 * (1 + T) ^ k) ^ 2 * E ^ 2)) +
      (1 + 1 / ϑ) * (K4 * (c1G n d k CF T / n * E) ^ 2) = cVX n d k CF K4 KX T ϑ / n * E ^ 2 := by
    intro E; unfold cVX
    generalize c1G n d k CF T = c
    generalize ((1 + T) ^ (2 * k) + (T / k) ^ 2 * (1 + T) ^ k) = Q
    field_simp
  generalize en k (eD d) A = E at *
  generalize g0P d P = g at *
  obtain ⟨P2, hP2def⟩ : ∃ P2 : MvPolynomial (Fin n) ℝ, P2 = (P - MvPolynomial.C g) ^ 2 :=
    ⟨_, rfl⟩
  have hP2 : P2.totalDegree ≤ 2 * k := by
    rw [hP2def]
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    have : (P - MvPolynomial.C g).totalDegree ≤ k :=
      (MvPolynomial.totalDegree_sub _ _).trans (by simp [hP])
    exact Nat.mul_le_mul_left 2 this
  have hFW2 : ∀ (W : WIdx n d → ℝ) (x : Fin n → ℝ),
      FW P2 lam W x = (FW P lam W x - g) ^ 2 := by
    intro W x; rw [hP2def]; simp [FW]
  obtain ⟨hQx, QB, hQBd, hQB⟩ := hPoly k P hP lam
  obtain ⟨-, QX, hQXd, hQX⟩ := hPoly (2 * k) P2 hP2 lam
  obtain ⟨fF, fB, fE⟩ := hFub P lam
  obtain ⟨fF2, fB2, fE2⟩ := hFub P2 lam
  obtain ⟨iD, hD⟩ := hDec k P hP lam
  obtain ⟨iDX, hDX⟩ := hDec (2 * k) P2 hP2 lam
  have degsub : ∀ Q : MvPolynomial (WIdx n d) ℝ, Q.totalDegree ≤ k →
      (Q - MvPolynomial.C g).totalDegree ≤ k := fun Q hQ =>
    (MvPolynomial.totalDegree_sub _ _).trans (by simp [hQ])
  have ic : ∀ (Q : MvPolynomial (WIdx n d) ℝ) (f : (WIdx n d → ℝ) → ℝ),
      (∀ W, f W = MvPolynomial.eval W Q) → Integrable f (stdGauss (WIdx n d)) := fun Q f h => by
    rw [show f = fun W => MvPolynomial.eval W Q from funext h]
    exact BstLean.Part59.gaussian_eval_integrable59x Q
  have herrQ : ∀ W : WIdx n d → ℝ,
      errW P lam W = MvPolynomial.eval W (QB - MvPolynomial.C g) := fun W => by
    rw [herrdef, map_sub, MvPolynomial.eval_C, hQB]
  have ierr2 : Integrable (fun W : WIdx n d → ℝ => errW P lam W ^ 2) (stdGauss (WIdx n d)) :=
    ic ((QB - MvPolynomial.C g) ^ 2) _ (fun W => by simp only [map_pow, herrQ])
  have ierr4 : Integrable (fun W : WIdx n d → ℝ => (errW P lam W ^ 2) ^ 2)
      (stdGauss (WIdx n d)) :=
    ic (((QB - MvPolynomial.C g) ^ 2) ^ 2) _ (fun W => by simp only [map_pow, herrQ])
  -- Step 3: the error
  have hDv : (fun x : Fin n → ℝ => ∫ W : WIdx n d → ℝ,
      (FW P lam W x - ∫ W' : WIdx n d → ℝ, FW P lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d)) = fun x => en k (lam ^ 2 * kap d x x) A := by
    funext x
    rw [(h3 lam x).2, (hS0 x _).2]; simp
  rw [hDv] at hD
  have hbar : (∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d)) - g =
      ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ∂uniformSphere n := by
    have e1 : (fun x : Fin n → ℝ => ∫ W : WIdx n d → ℝ, FW P lam W x ∂stdGauss (WIdx n d)) =
        fun x => (hmean k (lam ^ 2 * kap d x x) A - g) + g := by
      funext x; rw [(h3 lam x).2]; ring
    have e2 : ∫ x : Fin n → ℝ, ((hmean k (lam ^ 2 * kap d x x) A - g) + g) ∂uniformSphere n =
        ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ∂uniformSphere n +
          ∫ _x : Fin n → ℝ, g ∂uniformSphere n := integral_add im (integrable_const g)
    rw [fE, e1, e2, integral_const]; simp
  generalize hbb : (∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d)) = bbar at *
  have hb2 : (bbar - g) ^ 2 ≤ (T / k) ^ 2 * (1 + T) ^ k * E := by
    rw [hbar]
    exact (sq_integral_le _ _ im iq).trans Hq
  have hcfn : 0 ≤ CF / (eD d * n) := div_nonneg hCF (mul_pos he0 hn0).le
  have hD' : ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ^ 2 ∂stdGauss (WIdx n d) ≤
      CF / (eD d * n) * ((1 + T) ^ (2 * k) * E) :=
    hD.trans (mul_le_mul_of_nonneg_left Hv hcfn)
  have iBc : Integrable (fun W : WIdx n d → ℝ => BW P lam W - bbar) (stdGauss (WIdx n d)) :=
    fB.sub (integrable_const _)
  have hBc0 : ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ∂stdGauss (WIdx n d) = 0 := by
    have h1 : ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ∂stdGauss (WIdx n d) =
        ∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d) -
          ∫ _W : WIdx n d → ℝ, bbar ∂stdGauss (WIdx n d) :=
      integral_sub fB (integrable_const _)
    rw [h1, integral_const, hbb]; simp
  have Herr0 : ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d) =
      ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ^ 2 ∂stdGauss (WIdx n d) + (bbar - g) ^ 2 := by
    have h := (sq_shift_integral (stdGauss (WIdx n d)) (fun W => BW P lam W - bbar) iBc iD
      (g - bbar)).2
    have e : (fun W : WIdx n d → ℝ => errW P lam W ^ 2) =
        fun W => (BW P lam W - bbar - (g - bbar)) ^ 2 := by
      funext W; rw [herrdef]; ring
    rw [e, h, hBc0]; ring
  have Herr : ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d) ≤
      c1G n d k CF T / n * E := by
    rw [Herr0, hc1e]; linarith
  have Hq' : ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 ∂uniformSphere n ≤
      c1G n d k CF T / n * E := by
    rw [hc1e]
    have : 0 ≤ CF / (eD d * n) * ((1 + T) ^ (2 * k) * E) :=
      mul_nonneg hcfn (mul_nonneg hpe hE)
    linarith
  -- Step 4: the floor
  have hVW : ∀ W : WIdx n d → ℝ, VW P lam W = BW P2 lam W - errW P lam W ^ 2 := by
    intro W
    have i2 : Integrable (fun x : Fin n → ℝ => (FW P lam W x - g) ^ 2) (uniformSphere n) := by
      have : Integrable (fun x : Fin n → ℝ => FW P2 lam W x) (uniformSphere n) := fF2 W
      simpa only [hFW2] using this
    have h := (sq_shift_integral (uniformSphere n) (fun x => FW P lam W x - g)
      ((fF W).sub (integrable_const g)) i2 (errW P lam W)).2
    have e1 : ∫ x : Fin n → ℝ, (FW P lam W x - g) ∂uniformSphere n = errW P lam W := by
      have h1 : ∫ x : Fin n → ℝ, (FW P lam W x - g) ∂uniformSphere n =
          ∫ x : Fin n → ℝ, FW P lam W x ∂uniformSphere n - ∫ _x : Fin n → ℝ, g ∂uniformSphere n :=
        integral_sub (fF W) (integrable_const g)
      rw [h1, integral_const, herrdef]; simp [BW]
    have e2 : ∫ x : Fin n → ℝ, (FW P lam W x - g) ^ 2 ∂uniformSphere n = BW P2 lam W := by
      unfold BW; simp only [hFW2]
    have e3 : VW P lam W =
        ∫ x : Fin n → ℝ, (FW P lam W x - g - errW P lam W) ^ 2 ∂uniformSphere n := by
      unfold VW varU
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [herrdef, BW]; ring
    rw [e3, h, e1, e2]; ring
  have hXint : ∫ W : WIdx n d → ℝ, BW P2 lam W ∂stdGauss (WIdx n d) =
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n +
        ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 ∂uniformSphere n := by
    have e1 : (fun x : Fin n → ℝ => ∫ W : WIdx n d → ℝ, FW P2 lam W x ∂stdGauss (WIdx n d)) =
        fun x => en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 := by
      funext x; simp only [hFW2]; exact (hS0 x g).2
    rw [fE2, e1]
    exact integral_add iv iq
  -- Step 5: the variance of `V`
  have hG : ∀ x : Fin n → ℝ, ∫ W : WIdx n d → ℝ,
      (FW P2 lam W x - ∫ W' : WIdx n d → ℝ, FW P2 lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d) ≤
      K4 * (en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 := by
    intro x
    obtain ⟨Q, hQd, hQ⟩ := hQx x
    have hfq : ∀ W : WIdx n d → ℝ,
        FW P2 lam W x = MvPolynomial.eval W ((Q - MvPolynomial.C g) ^ 2) := fun W => by
      rw [hFW2, map_pow, map_sub, MvPolynomial.eval_C, hQ]
    have i1 : Integrable (fun W : WIdx n d → ℝ => FW P2 lam W x) (stdGauss (WIdx n d)) :=
      ic _ _ hfq
    have i2 : Integrable (fun W : WIdx n d → ℝ => FW P2 lam W x ^ 2) (stdGauss (WIdx n d)) :=
      ic (((Q - MvPolynomial.C g) ^ 2) ^ 2) _ (fun W => by simp only [map_pow, hfq])
    have h44 := h4 (WIdx n d) (Q - MvPolynomial.C g) (degsub Q hQd)
    have e4 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (Q - MvPolynomial.C g) ^ 4) =
        fun W => FW P2 lam W x ^ 2 := by
      funext W; rw [hFW2, map_sub, MvPolynomial.eval_C, hQ]; ring
    have e2 : ∫ W : WIdx n d → ℝ, MvPolynomial.eval W (Q - MvPolynomial.C g) ^ 2
        ∂stdGauss (WIdx n d) =
        en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 := by
      rw [← (hS0 x g).2]
      refine integral_congr_ae (ae_of_all _ fun W => ?_)
      simp only [map_sub, MvPolynomial.eval_C, hQ]
    rw [e4, e2] at h44
    exact (var_le_sq (stdGauss (WIdx n d)) _ i1 i2).trans h44
  have hGint : ∫ x : Fin n → ℝ, (∫ W : WIdx n d → ℝ,
      (FW P2 lam W x - ∫ W' : WIdx n d → ℝ, FW P2 lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d)) ∂uniformSphere n ≤
      K4 * (((1 + T) ^ (2 * k) + (T / k) ^ 2 * (1 + T) ^ k) ^ 2 * E ^ 2) :=
    calc ∫ x : Fin n → ℝ, (∫ W : WIdx n d → ℝ,
          (FW P2 lam W x - ∫ W' : WIdx n d → ℝ, FW P2 lam W' x ∂stdGauss (WIdx n d)) ^ 2
          ∂stdGauss (WIdx n d)) ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, K4 * (en k (lam ^ 2 * kap d x x) A +
            (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 ∂uniformSphere n :=
          integral_mono_of_nonneg
            (ae_of_all _ fun x => integral_nonneg fun W => sq_nonneg _)
            (ivq.const_mul K4) (ae_of_all _ hG)
      _ = K4 * ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
            (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 ∂uniformSphere n :=
          integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left Hvq hK4
  have hXvar : ∫ W : WIdx n d → ℝ,
      (BW P2 lam W - ∫ W' : WIdx n d → ℝ, BW P2 lam W' ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d) ≤
      KX / n * (((1 + T) ^ (2 * k) + (T / k) ^ 2 * (1 + T) ^ k) ^ 2 * E ^ 2) := by
    rw [← hP2def] at hXV0
    exact hXV0.trans (mul_le_mul_of_nonneg_left Hvq (div_nonneg hKX hn0.le))
  have hY2 : ∫ W : WIdx n d → ℝ, (errW P lam W ^ 2) ^ 2 ∂stdGauss (WIdx n d) ≤
      K4 * (c1G n d k CF T / n * E) ^ 2 := by
    have h44 := h4 (WIdx n d) (QB - MvPolynomial.C g) (degsub QB hQBd)
    have e4 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (QB - MvPolynomial.C g) ^ 4) =
        fun W => (errW P lam W ^ 2) ^ 2 := by
      funext W; rw [← herrQ]; ring
    have e2 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (QB - MvPolynomial.C g) ^ 2) =
        fun W => errW P lam W ^ 2 := by
      funext W; rw [← herrQ]
    rw [e4, e2] at h44
    exact h44.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun W => sq_nonneg _) Herr 2) hK4)
  have hYvar := var_le_sq (stdGauss (WIdx n d)) (fun W => errW P lam W ^ 2) ierr2 ierr4
  have hVQ : ∀ W : WIdx n d → ℝ, VW P lam W =
      MvPolynomial.eval W (QX - (QB - MvPolynomial.C g) ^ 2) := fun W => by
    rw [hVW, map_sub, map_pow, hQX, ← herrQ]
  generalize (∫ W : WIdx n d → ℝ, BW P2 lam W ∂stdGauss (WIdx n d)) = Xb at *
  generalize hYb : (∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d)) = Yb at *
  have iYc : Integrable (fun W : WIdx n d → ℝ => (errW P lam W ^ 2 - Yb) ^ 2)
      (stdGauss (WIdx n d)) :=
    (sq_shift_integral (stdGauss (WIdx n d)) (fun W => errW P lam W ^ 2) ierr2 ierr4 Yb).1
  have iV : Integrable (fun W : WIdx n d → ℝ => (VW P lam W - (Xb - Yb)) ^ 2)
      (stdGauss (WIdx n d)) :=
    ic ((QX - (QB - MvPolynomial.C g) ^ 2 - MvPolynomial.C (Xb - Yb)) ^ 2) _
      (fun W => by simp only [map_pow, map_sub, MvPolynomial.eval_C, hVQ])
  have HV : ∫ W : WIdx n d → ℝ, (VW P lam W - (Xb - Yb)) ^ 2 ∂stdGauss (WIdx n d) ≤
      cVX n d k CF K4 KX T ϑ / n * E ^ 2 := by
    have hsum : ∫ W : WIdx n d → ℝ, ((1 + ϑ) * (BW P2 lam W - Xb) ^ 2 +
        (1 + 1 / ϑ) * (errW P lam W ^ 2 - Yb) ^ 2) ∂stdGauss (WIdx n d) =
        (1 + ϑ) * ∫ W : WIdx n d → ℝ, (BW P2 lam W - Xb) ^ 2 ∂stdGauss (WIdx n d) +
        (1 + 1 / ϑ) * ∫ W : WIdx n d → ℝ, (errW P lam W ^ 2 - Yb) ^ 2 ∂stdGauss (WIdx n d) := by
      have h1 : ∫ W : WIdx n d → ℝ, ((1 + ϑ) * (BW P2 lam W - Xb) ^ 2 +
          (1 + 1 / ϑ) * (errW P lam W ^ 2 - Yb) ^ 2) ∂stdGauss (WIdx n d) =
          ∫ W : WIdx n d → ℝ, (1 + ϑ) * (BW P2 lam W - Xb) ^ 2 ∂stdGauss (WIdx n d) +
          ∫ W : WIdx n d → ℝ, (1 + 1 / ϑ) * (errW P lam W ^ 2 - Yb) ^ 2 ∂stdGauss (WIdx n d) :=
        integral_add (iDX.const_mul (1 + ϑ)) (iYc.const_mul (1 + 1 / ϑ))
      rw [h1, integral_const_mul, integral_const_mul]
    have hpw : ∀ W : WIdx n d → ℝ, (VW P lam W - (Xb - Yb)) ^ 2 ≤
        (1 + ϑ) * (BW P2 lam W - Xb) ^ 2 + (1 + 1 / ϑ) * (errW P lam W ^ 2 - Yb) ^ 2 := by
      intro W
      rw [hVW]
      have := sq_sub_le_theta (BW P2 lam W - Xb) (errW P lam W ^ 2 - Yb) ϑ hϑ
      have e : BW P2 lam W - errW P lam W ^ 2 - (Xb - Yb) =
          BW P2 lam W - Xb - (errW P lam W ^ 2 - Yb) := by ring
      rw [e]; exact this
    calc ∫ W : WIdx n d → ℝ, (VW P lam W - (Xb - Yb)) ^ 2 ∂stdGauss (WIdx n d)
        ≤ ∫ W : WIdx n d → ℝ, ((1 + ϑ) * (BW P2 lam W - Xb) ^ 2 +
            (1 + 1 / ϑ) * (errW P lam W ^ 2 - Yb) ^ 2) ∂stdGauss (WIdx n d) :=
          integral_mono_ae iV ((iDX.const_mul (1 + ϑ)).add (iYc.const_mul (1 + 1 / ϑ))) (ae_of_all _ hpw)
      _ = (1 + ϑ) * ∫ W : WIdx n d → ℝ, (BW P2 lam W - Xb) ^ 2 ∂stdGauss (WIdx n d) +
          (1 + 1 / ϑ) * ∫ W : WIdx n d → ℝ, (errW P lam W ^ 2 - Yb) ^ 2 ∂stdGauss (WIdx n d) := hsum
      _ ≤ (1 + ϑ) * (KX / n *
            (((1 + T) ^ (2 * k) + (T / k) ^ 2 * (1 + T) ^ k) ^ 2 * E ^ 2)) +
          (1 + 1 / ϑ) * (K4 * (c1G n d k CF T / n * E) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hXvar (by positivity))
            (mul_le_mul_of_nonneg_left (hYvar.trans hY2) (by positivity))
      _ = cVX n d k CF K4 KX T ϑ / n * E ^ 2 := hcVe E
  rw [hXint] at iV HV
  exact ⟨ierr2, Hq', Hv, Hfl, Herr, iV, HV⟩

/-- **The Gaussian model given the constant column, on the scale window.** -/
theorem gaussModel88 (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 10 ≤ n) (w B CF K4 KX ϑ : ℝ)
    (hϑ : 0 < ϑ) (hKX : 0 ≤ KX) (hXV : XVar n d k w KX) (hw0 : 0 ≤ w) (hw : w / (n : ℝ) ≤ 1 / 10) (hB : 0 ≤ B) (hCF : 0 ≤ CF) (hK4 : 0 ≤ K4)
    (hRep : RepIface n d) (hSc : ScaleIface n k) (hDec : DecorIface n d CF) (hFub : FubIface n d)
    (hPt : PtIface88 n d k w) (hMF : MomFacts88 n d k w B) (hPoly : PolyRep n d)
    (h4 : Fourth84 k K4) :
    GM88 n d k w (c1G n d k CF (tauF n d k w B)) (cVX n d k CF K4 KX (tauF n d k w B) ϑ)
      (eflG n d k CF (tauF n d k w B)) (cEG k (tauF n d k w B)) := by
  intro P hP
  have hn1 : 1 ≤ n := by omega
  obtain ⟨A, hR⟩ := hRep k P hP
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have hE : 0 ≤ en k (eD d) A := en_nonneg _ (by linarith) A
  have per := fun lam hlam =>
    perLam hd hk hn w B CF K4 KX ϑ hϑ hKX hXV hw0 hw hCF hK4 hSc hDec hFub hPt hMF hPoly h4 P hP A hR lam hlam
  refine ⟨en k (eD d) A, fun lam =>
    ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n +
      ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2 ∂uniformSphere n -
      ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d), hE, ?_, ?_⟩
  · intro lam hlam
    obtain ⟨ierr2, Hq', Hv, Hfl, Herr, iV, HV⟩ := per lam hlam
    refine ⟨?_, ierr2, iV, Herr, HV⟩
    beta_reduce
    have hq0 : 0 ≤ ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2
        ∂uniformSphere n := integral_nonneg fun x => sq_nonneg _
    have e : (1 - eflG n d k CF (tauF n d k w B)) * en k (eD d) A =
        (1 - 2 * k * tauF n d k w B) * en k (eD d) A -
          c1G n d k CF (tauF n d k w B) / n * en k (eD d) A := by
      unfold eflG; ring
    rw [e]; linarith
  · intro lam lam' hlam hlam'
    obtain ⟨-, Hq, Hv, -, Herr, -, -⟩ := per lam hlam
    obtain ⟨-, Hq', Hv', -, Herr', -, -⟩ := per lam' hlam'
    have D1 := enDrift hd hn1 w hw0 hw hSc hPt A hR.1 lam lam' hlam hlam'
    have D2 := enDrift hd hn1 w hw0 hw hSc hPt A hR.1 lam' lam hlam' hlam
    rw [abs_sub_comm, min_comm] at D2
    have hq0 : 0 ≤ ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2
        ∂uniformSphere n := integral_nonneg fun x => sq_nonneg _
    have hq0' : 0 ≤ ∫ x : Fin n → ℝ, (hmean k (lam' ^ 2 * kap d x x) A - g0P d P) ^ 2
        ∂uniformSphere n := integral_nonneg fun x => sq_nonneg _
    have hy0 : 0 ≤ ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d) :=
      integral_nonneg fun x => sq_nonneg _
    have hy0' : 0 ≤ ∫ W : WIdx n d → ℝ, errW P lam' W ^ 2 ∂stdGauss (WIdx n d) :=
      integral_nonneg fun x => sq_nonneg _
    have ht0 : 0 ≤ |lam' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (lam' ^ 2) :=
      div_nonneg (by positivity) (le_min (sq_nonneg _) (sq_nonneg _))
    have hM : 1 ≤ (1 + k * (|lam' ^ 2 - lam ^ 2| * Real.sqrt n /
        min (lam ^ 2) (lam' ^ 2))) ^ (2 * k) :=
      one_le_pow₀ (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) ht0])
    beta_reduce
    unfold cEG
    generalize (1 + k * (|lam' ^ 2 - lam ^ 2| * Real.sqrt n /
        min (lam ^ 2) (lam' ^ 2))) ^ (2 * k) = M at *
    generalize c1G n d k CF (tauF n d k w B) = c at *
    generalize (1 + tauF n d k w B) ^ (2 * k) = cE at *
    generalize en k (eD d) A = E at *
    generalize (∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n) = I at *
    generalize (∫ x : Fin n → ℝ, en k (lam' ^ 2 * kap d x x) A ∂uniformSphere n) = I' at *
    have a1 : (M - 1) * I ≤ (M - 1) * (cE * E) := mul_le_mul_of_nonneg_left Hv (by linarith)
    have a2 : (M - 1) * I' ≤ (M - 1) * (cE * E) := mul_le_mul_of_nonneg_left Hv' (by linarith)
    have e : ((M - 1) * cE + 2 * c / n) * E = (M - 1) * (cE * E) + 2 * (c / n * E) := by ring
    rw [e, abs_le]
    constructor <;> linarith

/-- The variance of `(F_x − g)²` over `W` is at most `K4 (E_W (F_x − g)²)²`. -/
lemma varG_le (hPoly : PolyRep n d) (K4 : ℝ) (h4 : Fourth84 k K4)
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ k) (A : Tens n) (hR : Rep84 n d k P A)
    (g lam : ℝ) (x : Fin n → ℝ) :
    ∫ W : WIdx n d → ℝ,
      (FW ((P - MvPolynomial.C g) ^ 2) lam W x -
        ∫ W' : WIdx n d → ℝ, FW ((P - MvPolynomial.C g) ^ 2) lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d) ≤
      K4 * (en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 := by
  have hS0 := step0 hR lam
  obtain ⟨hQx, -⟩ := hPoly k P hP lam
  have hFW2 : ∀ (W : WIdx n d → ℝ) (x : Fin n → ℝ),
      FW ((P - MvPolynomial.C g) ^ 2) lam W x = (FW P lam W x - g) ^ 2 := by
    intro W x; simp [FW]
  have degsub : ∀ Q : MvPolynomial (WIdx n d) ℝ, Q.totalDegree ≤ k →
      (Q - MvPolynomial.C g).totalDegree ≤ k := fun Q hQ =>
    (MvPolynomial.totalDegree_sub _ _).trans (by simp [hQ])
  have ic : ∀ (Q : MvPolynomial (WIdx n d) ℝ) (f : (WIdx n d → ℝ) → ℝ),
      (∀ W, f W = MvPolynomial.eval W Q) → Integrable f (stdGauss (WIdx n d)) := fun Q f h => by
    rw [show f = fun W => MvPolynomial.eval W Q from funext h]
    exact BstLean.Part59.gaussian_eval_integrable59x Q
  obtain ⟨Q, hQd, hQ⟩ := hQx x
  have hfq : ∀ W : WIdx n d → ℝ,
      FW ((P - MvPolynomial.C g) ^ 2) lam W x =
        MvPolynomial.eval W ((Q - MvPolynomial.C g) ^ 2) := fun W => by
    rw [hFW2, map_pow, map_sub, MvPolynomial.eval_C, hQ]
  have i1 : Integrable (fun W : WIdx n d → ℝ => FW ((P - MvPolynomial.C g) ^ 2) lam W x)
      (stdGauss (WIdx n d)) := ic _ _ hfq
  have i2 : Integrable (fun W : WIdx n d → ℝ => FW ((P - MvPolynomial.C g) ^ 2) lam W x ^ 2)
      (stdGauss (WIdx n d)) :=
    ic (((Q - MvPolynomial.C g) ^ 2) ^ 2) _ (fun W => by simp only [map_pow, hfq])
  have h44 := h4 (WIdx n d) (Q - MvPolynomial.C g) (degsub Q hQd)
  have e4 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (Q - MvPolynomial.C g) ^ 4) =
      fun W => FW ((P - MvPolynomial.C g) ^ 2) lam W x ^ 2 := by
    funext W; rw [hFW2, map_sub, MvPolynomial.eval_C, hQ]; ring
  have e2 : ∫ W : WIdx n d → ℝ, MvPolynomial.eval W (Q - MvPolynomial.C g) ^ 2
      ∂stdGauss (WIdx n d) =
      en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 := by
    rw [← (hS0 x g).2]
    refine integral_congr_ae (ae_of_all _ fun W => ?_)
    simp only [map_sub, MvPolynomial.eval_C, hQ]
  rw [e4, e2] at h44
  exact (var_le_sq (stdGauss (WIdx n d)) _ i1 i2).trans h44

/-- Integrability over the sphere of `(E_W (F_x − g)²)²`. -/
lemma int_m2sq (hn : 1 ≤ n) (A : Tens n) (g lam : ℝ) :
    Integrable (fun x : Fin n → ℝ => (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2) (uniformSphere n) := by
  have hcs : Continuous (fun x : Fin n → ℝ => lam ^ 2 * kap d x x) :=
    continuous_const.mul (BstLean.Part81.cont_kap_diag d)
  have hcv := cont_en (k := k) A _ hcs
  have hcm := (cont_hmean (k := k) A _ hcs).sub (continuous_const (y := g))
  exact BstLean.Part78.sph_int hn ((hcv.add (hcm.pow 2)).pow 2)

/-- The hypothesis `XVar` with the constant of Part 84: `KX = CF · K4 / e_d`. -/
theorem xvar_old (hn : 1 ≤ n) (hd : 1 ≤ d) (w CF K4 : ℝ) (hCF : 0 ≤ CF) (hK4 : 0 ≤ K4)
    (hDec : DecorIface n d CF) (hPoly : PolyRep n d) (h4 : Fourth84 k K4) :
    XVar n d k w (CF * K4 / eD d) := by
  intro P hP A hR lam _
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have he0 : 0 < eD d := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hP2 : ((P - MvPolynomial.C (g0P d P)) ^ 2).totalDegree ≤ 2 * k := by
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    have : (P - MvPolynomial.C (g0P d P)).totalDegree ≤ k :=
      (MvPolynomial.totalDegree_sub _ _).trans (by simp [hP])
    exact Nat.mul_le_mul_left 2 this
  obtain ⟨-, hDX⟩ := hDec (2 * k) _ hP2 lam
  have hcfn : 0 ≤ CF / (eD d * n) := div_nonneg hCF (mul_pos he0 hn0).le
  refine hDX.trans ?_
  have hGint : ∫ x : Fin n → ℝ, (∫ W : WIdx n d → ℝ,
      (FW ((P - MvPolynomial.C (g0P d P)) ^ 2) lam W x -
        ∫ W' : WIdx n d → ℝ, FW ((P - MvPolynomial.C (g0P d P)) ^ 2) lam W' x
          ∂stdGauss (WIdx n d)) ^ 2 ∂stdGauss (WIdx n d)) ∂uniformSphere n ≤
      K4 * ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
        (hmean k (lam ^ 2 * kap d x x) A - g0P d P) ^ 2) ^ 2 ∂uniformSphere n := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg
      (ae_of_all _ fun x => integral_nonneg fun W => sq_nonneg _)
      ((int_m2sq hn A _ lam).const_mul K4)
      (ae_of_all _ fun x => varG_le hPoly K4 h4 P hP A hR _ lam x)
  refine (mul_le_mul_of_nonneg_left hGint hcfn).trans (le_of_eq ?_)
  field_simp

end BstLean.Part88

#print axioms BstLean.Part88.gaussModel88
