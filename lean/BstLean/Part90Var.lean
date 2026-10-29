import BstLean.Part90Defs
import BstLean.Part80VarBound
import BstLean.Part82VarA
import BstLean.Part78Poincare

/-!
# Part 90: the regularity `RegC` and the variance bound in one slice `VarBoundC`

Cubic `f`, an `x`-dependent mean field `mu`, a general distribution `ν` on the sphere.
Gaussian Poincaré inequality, the chain rule, Bessel with `FeatOpA`, a weighted Bessel step with
`Feat4A`, and Cauchy–Schwarz in `W` (in the form of the arithmetic–geometric mean inequality with
a free parameter `t`, so that every function of `W` that is integrated is a polynomial).
-/

namespace BstLean.Part90

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (nsq frobH zv PP gpi78)
open BstLean.Part80 (kA FeatOpA sph_int PP_int_x PP_int_prod PP_int besselVB)
open BstLean.Part82 (T3 SymT cfun aU3 HU3)
open BstLean.Part82.VarAux (chain_alg)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Real-variable lemmas -/

lemma split_sq (η a b : ℝ) (hη : 0 < η) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
  have h : (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 - (a + b) ^ 2 = (η * a - b) ^ 2 / η := by
    field_simp; ring
  have : 0 ≤ (η * a - b) ^ 2 / η := by positivity
  linarith

lemma amgm (t Y r : ℝ) (ht : 0 < t) : Y * r ≤ (t / 2) * Y ^ 2 + (1 / (2 * t)) * r ^ 2 := by
  have h : (t / 2) * Y ^ 2 + (1 / (2 * t)) * r ^ 2 - Y * r = (t * Y - r) ^ 2 / (2 * t) := by
    field_simp; ring
  have : 0 ≤ (t * Y - r) ^ 2 / (2 * t) := by positivity
  linarith

lemma half_aux (K e : ℝ) (hK : 0 ≤ K) (he : 0 < e) : K * e / (2 * (K + 1)) ≤ e / 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hK he.le]

/-- Optimization in the free parameter `t`. -/
lemma opt (X A c s Dd s2 d : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (hD : 0 ≤ Dd) (hs2 : s2 ≤ s ^ 2)
    (hd : d ≤ Dd ^ 4)
    (h : ∀ t : ℝ, 0 < t → X ≤ A + c * ((t / 2) * s2 + (1 / (2 * t)) * d)) :
    X ≤ A + c * s * Dd ^ 2 := by
  have h' : ∀ t : ℝ, 0 < t → X ≤ A + c * ((t / 2) * s ^ 2 + (1 / (2 * t)) * Dd ^ 4) := by
    intro t ht
    have a1 : (t / 2) * s2 ≤ (t / 2) * s ^ 2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
    have a2 : (1 / (2 * t)) * d ≤ (1 / (2 * t)) * Dd ^ 4 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have := mul_le_mul_of_nonneg_left (add_le_add a1 a2) hc
    linarith [h t ht]
  rcases hs.lt_or_eq with hs0 | hs0
  · rcases hD.lt_or_eq with hD0 | hD0
    · have ht : 0 < Dd ^ 2 / s := by positivity
      have := h' _ ht
      have e : (Dd ^ 2 / s / 2) * s ^ 2 + (1 / (2 * (Dd ^ 2 / s))) * Dd ^ 4 = s * Dd ^ 2 := by
        field_simp; ring
      rw [e] at this
      linarith
    · subst hD0
      by_contra hcon
      rw [not_le] at hcon
      have he : 0 < X - A := by nlinarith
      have hK : 0 ≤ c * s ^ 2 := by positivity
      have ht : 0 < (X - A) / (c * s ^ 2 + 1) := by positivity
      have := h' _ ht
      have e : c * (((X - A) / (c * s ^ 2 + 1) / 2) * s ^ 2 +
          (1 / (2 * ((X - A) / (c * s ^ 2 + 1)))) * (0 : ℝ) ^ 4) =
          (c * s ^ 2) * (X - A) / (2 * (c * s ^ 2 + 1)) := by
        field_simp; ring
      rw [e] at this
      have := half_aux _ _ hK he
      linarith
  · subst hs0
    by_contra hcon
    rw [not_le] at hcon
    have he : 0 < X - A := by nlinarith
    have hK : 0 ≤ c * Dd ^ 4 := by positivity
    have ht : 0 < (c * Dd ^ 4 + 1) / (X - A) := by positivity
    have := h' _ ht
    have e : c * (((c * Dd ^ 4 + 1) / (X - A) / 2) * (0 : ℝ) ^ 2 +
        (1 / (2 * ((c * Dd ^ 4 + 1) / (X - A)))) * Dd ^ 4) =
        (c * Dd ^ 4) * (X - A) / (2 * (c * Dd ^ 4 + 1)) := by
      field_simp; ring
    rw [e] at this
    have := half_aux _ _ hK he
    linarith

/-! ### Cauchy–Schwarz and the two Bessel steps on the sphere -/

section sphere
variable {n : ℕ} {J : Type} [Fintype J] {ν : Measure (Fin n → ℝ)}

lemma cs_sph (hν : SphLaw n ν) {f g : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
  have hquad (t : ℝ) : 0 ≤ (∫ x, f x ^ 2 ∂ν) * (t * t) + (2 * ∫ x, f x * g x ∂ν) * t +
      ∫ x, g x ^ 2 ∂ν := by
    have h : 0 ≤ ∫ x, (t * f x + g x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : (fun x => (t * f x + g x) ^ 2) = fun x =>
        (t * t * f x ^ 2 + (2 * t) * (f x * g x)) + g x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t * t * f x ^ 2) ν := (sph_int hν (hf.pow 2)).const_mul _
    have i2 : Integrable (fun x => (2 * t) * (f x * g x)) ν :=
      (sph_int hν (hf.mul hg)).const_mul _
    have i3 : Integrable (fun x => g x ^ 2) ν := sph_int hν (hg.pow 2)
    have i12 : Integrable (fun x => t * t * f x ^ 2 + (2 * t) * (f x * g x)) ν := i1.add i2
    rw [he, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
      integral_const_mul] at h
    linarith
  have := discrim_le_zero hquad
  unfold discrim at this
  nlinarith

/-- The weighted Bessel step with the fourth-moment feature bound. -/
lemma weightedBessel (hν : SphLaw n ν) {ψ : (Fin n → ℝ) → J → ℝ} (hψ : Continuous ψ)
    (G4 : ℝ) (hG4 : 0 ≤ G4) (hF4 : Feat4A ν ψ G4)
    (Q : (Fin n → ℝ) → ℝ) (hQ : Continuous Q) (Dv : Fin n → (Fin n → ℝ) → ℝ)
    (hD : ∀ i, Continuous (Dv i)) :
    ∑ i, ∑ q : J, (∫ x, Q x * Dv i x * ψ x q ∂ν) ^ 2 ≤
      G4 * (∫ x, Q x ^ 2 ∂ν) * Real.sqrt (∫ x, (∑ i, Dv i x ^ 2) ^ 2 ∂ν) := by
  have hprob := hν.prob
  have hψq (q : J) : Continuous fun x => ψ x q := (continuous_apply q).comp hψ
  obtain ⟨c, hc⟩ : ∃ c : Fin n → J → ℝ, ∀ i q, c i q = ∫ x, Q x * Dv i x * ψ x q ∂ν :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin n → (Fin n → ℝ) → ℝ, ∀ i x, g i x = ∑ q, c i q * ψ x q :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : (Fin n → ℝ) → ℝ, ∀ x, N x = ∑ i, Dv i x ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨nc, hnc⟩ : ∃ nc : Fin n → ℝ, ∀ i, nc i = ∑ q, c i q ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, nc i := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ∫ x, Q x ^ 2 ∂ν := ⟨_, rfl⟩
  obtain ⟨d4, hd4⟩ : ∃ d4 : ℝ, d4 = ∫ x, N x ^ 2 ∂ν := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : (Fin n → ℝ) → ℝ, ∀ x, h x = ∑ i, Dv i x * g i x := ⟨_, fun _ => rfl⟩
  have hgc (i : Fin n) : Continuous (g i) := by
    have : g i = fun x => ∑ q, c i q * ψ x q := funext fun x => hg i x
    rw [this]; exact continuous_finsetSum _ fun q _ => continuous_const.mul (hψq q)
  have hNc : Continuous N := by
    have : N = fun x => ∑ i, Dv i x ^ 2 := funext hN
    rw [this]; exact continuous_finsetSum _ fun i _ => (hD i).pow 2
  have hhc : Continuous h := by
    have : h = fun x => ∑ i, Dv i x * g i x := funext hh
    rw [this]; exact continuous_finsetSum _ fun i _ => (hD i).mul (hgc i)
  have hN0 (x : Fin n → ℝ) : 0 ≤ N x := by
    rw [hN]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnc0 (i : Fin n) : 0 ≤ nc i := by
    rw [hnc]; exact Finset.sum_nonneg fun q _ => sq_nonneg _
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun i _ => hnc0 i
  have hY0 : 0 ≤ Y := by rw [hY]; exact integral_nonneg fun x => sq_nonneg _
  have hd0 : 0 ≤ d4 := by rw [hd4]; exact integral_nonneg fun x => sq_nonneg _
  -- (a) `S' = ∫ Q h`
  have ha : ∫ x, Q x * h x ∂ν = S := by
    have he : (fun x => Q x * h x) = fun x => ∑ i, ∑ q, c i q * (Q x * Dv i x * ψ x q) := by
      funext x; simp only [hh, hg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
    have hi (i : Fin n) (q : J) : Integrable (fun x => c i q * (Q x * Dv i x * ψ x q)) ν :=
      (sph_int hν ((hQ.mul (hD i)).mul (hψq q))).const_mul _
    rw [he, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun q _ => hi i q, hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun q _ => hi i q, hnc]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul, ← hc]; ring
  -- (b) Cauchy–Schwarz
  have hb : S ^ 2 ≤ Y * ∫ x, h x ^ 2 ∂ν := by
    rw [← ha, hY]; exact cs_sph hν hQ hhc
  -- (c) Cauchy–Schwarz in `i`
  have hcc : ∫ x, h x ^ 2 ∂ν ≤ ∑ i, ∫ x, N x * g i x ^ 2 ∂ν := by
    have hi (i : Fin n) : Integrable (fun x => N x * g i x ^ 2) ν :=
      sph_int hν (hNc.mul ((hgc i).pow 2))
    rw [← integral_finsetSum _ fun i _ => hi i]
    refine integral_mono (sph_int hν (hhc.pow 2)) (integrable_finsetSum _ fun i _ => hi i)
      fun x => ?_
    show h x ^ 2 ≤ ∑ i, N x * g i x ^ 2
    rw [← Finset.mul_sum, hh, hN]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- (d) the fourth moment
  have hd (i : Fin n) : ∫ x, N x * g i x ^ 2 ∂ν ≤ Real.sqrt d4 * G4 * nc i := by
    have h1 := cs_sph hν hNc ((hgc i).pow 2)
    have h2 : ∫ x, (g i x ^ 2) ^ 2 ∂ν ≤ G4 ^ 2 * nc i ^ 2 := by
      have h4 := hF4 (c i)
      have e : (fun x => (g i x ^ 2) ^ 2) = fun x => (∑ q, c i q * ψ x q) ^ 4 := by
        funext x; rw [hg i x]; ring
      rw [e, hnc i]; exact h4
    have hA0 : 0 ≤ ∫ x, N x * g i x ^ 2 ∂ν :=
      integral_nonneg fun x => mul_nonneg (hN0 x) (sq_nonneg _)
    have hB0 : 0 ≤ Real.sqrt d4 * G4 * nc i :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hG4) (hnc0 i)
    have hsq : (∫ x, N x * g i x ^ 2 ∂ν) ^ 2 ≤ (Real.sqrt d4 * G4 * nc i) ^ 2 := by
      calc (∫ x, N x * g i x ^ 2 ∂ν) ^ 2 ≤ d4 * ∫ x, (g i x ^ 2) ^ 2 ∂ν := by rw [hd4]; exact h1
        _ ≤ d4 * (G4 ^ 2 * nc i ^ 2) := mul_le_mul_of_nonneg_left h2 hd0
        _ = (Real.sqrt d4 * G4 * nc i) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hd0]; ring
    exact (pow_le_pow_iff_left₀ hA0 hB0 two_ne_zero).mp hsq
  -- (e)
  have he : S * S ≤ (G4 * Y * Real.sqrt d4) * S := by
    calc S * S = S ^ 2 := by ring
      _ ≤ Y * ∫ x, h x ^ 2 ∂ν := hb
      _ ≤ Y * ∑ i, (Real.sqrt d4 * G4 * nc i) :=
        mul_le_mul_of_nonneg_left (hcc.trans (Finset.sum_le_sum fun i _ => hd i)) hY0
      _ = (G4 * Y * Real.sqrt d4) * S := by rw [← Finset.mul_sum, ← hS]; ring
  have fin : S ≤ G4 * Y * Real.sqrt d4 := by
    rcases hS0.lt_or_eq with hpos | hz
    · exact le_of_mul_le_mul_right he hpos
    · rw [← hz]; exact mul_nonneg (mul_nonneg hG4 hY0) (Real.sqrt_nonneg _)
  simpa only [hS, hnc, hc, hY, hd4, hN] using fin

/-- Steps 3–5 for a fixed `W`: the gradient sum, with the split `G = Ā + (G − Ā)`. -/
lemma gradBound (hν : SphLaw n ν) {ψ : (Fin n → ℝ) → J → ℝ} (hψ : Continuous ψ)
    (Γ G4 : ℝ) (hΓ : 0 ≤ Γ) (hG4 : 0 ≤ G4) (hF : FeatOpA ν ψ Γ) (hF4 : Feat4A ν ψ G4)
    (Q : (Fin n → ℝ) → ℝ) (hQ : Continuous Q) (G : Fin n → (Fin n → ℝ) → ℝ)
    (hG : ∀ i, Continuous (G i)) (Abar : Fin n → ℝ) (η : ℝ) (hη : 0 < η) :
    ∑ i, ∑ q : J, (∫ x, Q x * G i x * ψ x q ∂ν) ^ 2 ≤
      (1 + η) * nsq Abar * Γ * (∫ x, Q x ^ 2 ∂ν) +
        (1 + 1 / η) * (G4 * (∫ x, Q x ^ 2 ∂ν) *
          Real.sqrt (∫ x, (∑ i, (G i x - Abar i) ^ 2) ^ 2 ∂ν)) := by
  have hψq (q : J) : Continuous fun x => ψ x q := (continuous_apply q).comp hψ
  have hW := weightedBessel hν hψ G4 hG4 hF4 Q hQ (fun i x => G i x - Abar i)
    (fun i => (hG i).sub continuous_const)
  have hB := besselVB hν hψ Γ hΓ hF Q hQ
  have hsplit (i : Fin n) (q : J) : ∫ x, Q x * G i x * ψ x q ∂ν =
      Abar i * (∫ x, Q x * ψ x q ∂ν) + ∫ x, Q x * (G i x - Abar i) * ψ x q ∂ν := by
    have j1 : Integrable (fun x => Abar i * (Q x * ψ x q)) ν :=
      (sph_int hν (hQ.mul (hψq q))).const_mul _
    have j2 : Integrable (fun x => Q x * (G i x - Abar i) * ψ x q) ν :=
      sph_int hν ((hQ.mul ((hG i).sub continuous_const)).mul (hψq q))
    rw [← integral_const_mul, ← integral_add j1 j2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have h1 (i : Fin n) (q : J) : (∫ x, Q x * G i x * ψ x q ∂ν) ^ 2 ≤
      (1 + η) * (Abar i ^ 2 * (∫ x, Q x * ψ x q ∂ν) ^ 2) +
        (1 + 1 / η) * (∫ x, Q x * (G i x - Abar i) * ψ x q ∂ν) ^ 2 := by
    rw [hsplit, ← mul_pow]; exact split_sq η _ _ hη
  have hn0 : 0 ≤ nsq Abar := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hη0 : 0 ≤ 1 + η := by positivity
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  calc ∑ i, ∑ q : J, (∫ x, Q x * G i x * ψ x q ∂ν) ^ 2
      ≤ ∑ i, ∑ q : J, ((1 + η) * (Abar i ^ 2 * (∫ x, Q x * ψ x q ∂ν) ^ 2) +
        (1 + 1 / η) * (∫ x, Q x * (G i x - Abar i) * ψ x q ∂ν) ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun q _ => h1 i q
    _ = (1 + η) * (nsq Abar * ∑ q : J, (∫ x, Q x * ψ x q ∂ν) ^ 2) +
        (1 + 1 / η) * ∑ i, ∑ q : J, (∫ x, Q x * (G i x - Abar i) * ψ x q ∂ν) ^ 2 := by
        simp only [nsq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ _ := by
        have a1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hn0) hη0
        have a2 := mul_le_mul_of_nonneg_left hW hη1
        linarith

end sphere

/-! ### The data and the polynomials -/

/-- The data of the abstract cubic conditional model. -/
structure DatC (n : ℕ) (J : Type) [Fintype J] where
  ν : Measure (Fin n → ℝ)
  hν : SphLaw n ν
  f0 : ℝ
  ℓ : Fin n → ℝ
  H : Matrix (Fin n) (Fin n) ℝ
  T : T3 n
  mu : (Fin n → ℝ) → Fin n → ℝ
  ψ : (Fin n → ℝ) → J → ℝ
  hmu : Continuous mu
  hψ : Continuous ψ

variable {n : ℕ} {J : Type} [Fintype J] (D : DatC n J)

lemma DatC.cψ (q : J) : Continuous fun x => D.ψ x q := (continuous_apply q).comp D.hψ
lemma DatC.cmu (i : Fin n) : Continuous fun x => D.mu x i := (continuous_apply i).comp D.hmu

/-- `z_i` as a polynomial in `W`. -/
noncomputable def ZpC (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (J × Fin n) ℝ :=
  ∑ q : J, C (D.ψ x q) * X (q, i)

/-- `mu_i(x) + z_i` as a polynomial in `W`. -/
noncomputable def YpC (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (J × Fin n) ℝ :=
  C (D.mu x i) + ZpC D x i

/-- `F_W(x)` as a polynomial in `W`. -/
noncomputable def FpC (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  C D.f0 + ∑ i, C (D.ℓ i) * YpC D x i + ∑ i, ∑ j, C (D.H i j) * YpC D x i * YpC D x j +
    ∑ i, ∑ j, ∑ k, C (D.T i j k) * YpC D x i * YpC D x j * YpC D x k

/-- `G_{x,i}(W) = ∇f(mu x + W ψ x)_i`. -/
def GvC (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) : ℝ :=
  aU3 D.ℓ D.H D.T (fun l => D.mu x l + zv W (D.ψ x) l) i

/-- `G_{x,i}` as a polynomial in `W`. -/
noncomputable def GpC (i : Fin n) (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  C (D.ℓ i) + C 2 * ∑ j, C (D.H i j) * YpC D x j +
    C 3 * ∑ j, ∑ k, C (D.T i j k) * YpC D x j * YpC D x k

@[simp] lemma eval_ZpC (x : Fin n → ℝ) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (ZpC D x i) = zv W (D.ψ x) i := by
  simp only [ZpC, zv, map_sum, map_mul, eval_C, eval_X]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

@[simp] lemma eval_YpC (x : Fin n → ℝ) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (YpC D x i) = D.mu x i + zv W (D.ψ x) i := by
  simp only [YpC, map_add, eval_C, eval_ZpC]

@[simp] lemma eval_FpC (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (FpC D x) = FC D.f0 D.ℓ D.H D.T D.mu D.ψ W x := by
  simp only [FpC, FC, cfun, map_sum, map_add, map_mul, eval_C, eval_YpC]

@[simp] lemma eval_GpC (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (GpC D i x) = GvC D i x W := by
  simp only [GpC, GvC, aU3, map_sum, map_add, map_mul, eval_C, eval_YpC]

lemma pderiv_ZpC (x : Fin n → ℝ) (q : J) (i j : Fin n) :
    pderiv (q, i) (ZpC D x j) = if j = i then C (D.ψ x q) else 0 := by
  classical
  simp only [ZpC, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, Pi.single_apply, Prod.mk.injEq,
    smul_eq_mul, mul_zero, add_zero]
  by_cases h : j = i <;> simp [h]

lemma eval_pderiv_YpC (x : Fin n → ℝ) (q : J) (i j : Fin n) (W : J × Fin n → ℝ) :
    eval W (pderiv (q, i) (YpC D x j)) = if j = i then D.ψ x q else 0 := by
  simp only [YpC, map_add, pderiv_C, zero_add, pderiv_ZpC]
  split_ifs <;> simp

/-- The chain rule. -/
lemma eval_pderiv_FpC (hH : D.H.IsSymm) (hT : SymT D.T) (x : Fin n → ℝ) (q : J) (i : Fin n)
    (W : J × Fin n → ℝ) :
    eval W (pderiv (q, i) (FpC D x)) = D.ψ x q * GvC D i x W := by
  classical
  have key := chain_alg D.ℓ D.H hH D.T hT (fun l => D.mu x l + zv W (D.ψ x) l) i (D.ψ x q)
    (fun j => eval W (pderiv (q, i) (YpC D x j))) (fun j => eval_pderiv_YpC D x q i j W)
  simp only [GvC, aU3]
  rw [← key]
  simp only [FpC, map_sum, map_add, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero,
    zero_mul, zero_add, map_mul, eval_C, eval_YpC]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · rfl
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => by ring

lemma PP_ZpC (i : Fin n) : PP 1 (fun x : Fin n → ℝ => ZpC D x i) := by
  unfold ZpC
  refine PP.sum _ fun q _ => ?_
  have := (PP.coef (ι := J × Fin n) (D.cψ q)).mul
    (PP.const (n := n) (d := 1) (X (q, i) : MvPolynomial (J × Fin n) ℝ) (by simp))
  simpa using this

lemma PP_CcC (c : ℝ) : PP (n := n) 0 (fun _ => (C c : MvPolynomial (J × Fin n) ℝ)) :=
  PP.const _ (by simp)

lemma PP_YpC (i : Fin n) : PP 1 (fun x : Fin n → ℝ => YpC D x i) := by
  unfold YpC
  exact ((PP.coef (ι := J × Fin n) (D.cmu i)).mono (by norm_num)).add (PP_ZpC D i)

lemma PP_FpC : PP 3 (FpC D) := by
  unfold FpC
  refine PP.add (PP.add (PP.add ((PP_CcC D.f0).mono (by norm_num)) (PP.sum _ fun i _ => ?_))
    (PP.sum _ fun i _ => PP.sum _ fun j _ => ?_))
    (PP.sum _ fun i _ => PP.sum _ fun j _ => PP.sum _ fun k _ => ?_)
  · exact (((PP_CcC (D.ℓ i)).mul (PP_YpC D i))).mono (by norm_num)
  · exact ((((PP_CcC (D.H i j)).mul (PP_YpC D i))).mul (PP_YpC D j)).mono (by norm_num)
  · exact (((((PP_CcC (D.T i j k)).mul (PP_YpC D i))).mul (PP_YpC D j)).mul
      (PP_YpC D k)).mono (by norm_num)

lemma PP_GpC (i : Fin n) : PP 2 (GpC D i) := by
  unfold GpC
  refine PP.add (PP.add ((PP_CcC (D.ℓ i)).mono (by norm_num)) ?_) ?_
  · have := (PP_CcC (n := n) (J := J) 2).mul
      (PP.sum Finset.univ fun j _ => (PP_CcC (D.H i j)).mul (PP_YpC D j))
    exact this.mono (by norm_num)
  · have := (PP_CcC (n := n) (J := J) 3).mul
      (PP.sum Finset.univ fun j _ => PP.sum Finset.univ fun k _ =>
        ((PP_CcC (D.T i j k)).mul (PP_YpC D j)).mul (PP_YpC D k))
    exact this.mono (by norm_num)

lemma cont_GvC (i : Fin n) (W : J × Fin n → ℝ) : Continuous fun x => GvC D i x W := by
  have := (PP_GpC D i).cont_x W
  simpa only [eval_GpC] using this

/-! ### The mean, `Q_x`, and `Y` as polynomials -/

/-- `E_y F_W(y)` as a polynomial in `W`. -/
noncomputable def FbarC : MvPolynomial (J × Fin n) ℝ := Classical.choose (PP_int (PP_FpC D) D.hν)

lemma FbarC_deg : (FbarC D).totalDegree ≤ 3 := (Classical.choose_spec (PP_int (PP_FpC D) D.hν)).1

lemma FbarC_eval (W : J × Fin n → ℝ) :
    eval W (FbarC D) = ∫ x, FC D.f0 D.ℓ D.H D.T D.mu D.ψ W x ∂D.ν := by
  have := (Classical.choose_spec (PP_int (PP_FpC D) D.hν)).2.1 W
  unfold FbarC
  simpa only [eval_FpC] using this

/-- `Q_x = F_x − E_y F_y`. -/
noncomputable def QpC (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ := FpC D x - FbarC D

lemma PP_QpC : PP 3 (QpC D) := (PP_FpC D).sub (PP.const _ (FbarC_deg D))

lemma QpC_mean (W : J × Fin n → ℝ) : ∫ x, eval W (QpC D x) ∂D.ν = 0 := by
  have := D.hν.prob
  have he : (fun x => eval W (QpC D x)) =
      fun x => FC D.f0 D.ℓ D.H D.T D.mu D.ψ W x - eval W (FbarC D) := by
    funext x; simp [QpC]
  have hi : Integrable (fun x => FC D.f0 D.ℓ D.H D.T D.mu D.ψ W x) D.ν := by
    have := PP_int_x (PP_FpC D) D.hν W
    simpa only [eval_FpC] using this
  rw [he, integral_sub hi (integrable_const _), integral_const, FbarC_eval]
  simp

/-- `Y` as a polynomial in `W`. -/
noncomputable def PVC : MvPolynomial (J × Fin n) ℝ :=
  Classical.choose (PP_int (PP_QpC D).sq D.hν)

lemma PVC_eval (W : J × Fin n → ℝ) :
    eval W (PVC D) = YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W := by
  have := (Classical.choose_spec (PP_int (PP_QpC D).sq D.hν)).2.1 W
  rw [PVC, this]
  simp [YC, varU, QpC, FbarC_eval]

lemma PVC_eval' (W : J × Fin n → ℝ) :
    YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W = ∫ x, (eval W (QpC D x)) ^ 2 ∂D.ν := by
  have := (Classical.choose_spec (PP_int (PP_QpC D).sq D.hν)).2.1 W
  rw [← PVC_eval D, PVC, this]
  simp

lemma cont_QG (i : Fin n) (W : J × Fin n → ℝ) :
    Continuous fun x => eval W (QpC D x) * GvC D i x W :=
  ((PP_QpC D).cont_x W).mul (cont_GvC D i W)

/-- The gradient of `Y`. -/
lemma PVC_grad (hH : D.H.IsSymm) (hT : SymT D.T) (q : J) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (pderiv (q, i) (PVC D)) =
      2 * ∫ x, (eval W (QpC D x) * GvC D i x W) * D.ψ x q ∂D.ν := by
  have h := (Classical.choose_spec (PP_int (PP_QpC D).sq D.hν)).2.2 (q, i) W
  rw [PVC, h]
  set cW := eval W (pderiv (q, i) (FbarC D)) with hcW
  have e : (fun x => eval W (pderiv (q, i) (QpC D x ^ 2))) = fun x =>
      2 * ((eval W (QpC D x) * GvC D i x W) * D.ψ x q) - (2 * cW) * eval W (QpC D x) := by
    funext x
    have h1 : eval W (pderiv (q, i) (QpC D x)) = D.ψ x q * GvC D i x W - cW := by
      simp only [QpC, map_sub, eval_pderiv_FpC D hH hT, hcW]
    rw [pow_two, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, h1]
    ring
  have i1 : Integrable (fun x => 2 * ((eval W (QpC D x) * GvC D i x W) * D.ψ x q)) D.ν :=
    (sph_int D.hν ((cont_QG D i W).mul (D.cψ q))).const_mul _
  have i2 : Integrable (fun x => (2 * cW) * eval W (QpC D x)) D.ν :=
    (PP_int_x (PP_QpC D) D.hν W).const_mul _
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, QpC_mean]
  ring

/-! ### Regularity -/

lemma regC_D : Integrable (YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ) (stdGauss (J × Fin n)) ∧
    Integrable (fun W => YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2) (stdGauss (J × Fin n)) := by
  have e : YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ = fun W => eval W (PVC D) :=
    funext fun W => (PVC_eval D W).symm
  rw [e]
  exact ⟨gauss_poly_integrable _, gpi78 _ 2⟩

/-- **Regularity** of `Y` in `W`. -/
theorem regC : RegC := by
  intro n J _ ν hν f0 ℓ H T mu ψ hmu hψ
  exact regC_D ⟨ν, hν, f0, ℓ, H, T, mu, ψ, hmu, hψ⟩

/-! ### The fourth moment of the gradient fluctuation, for a fixed `W` -/

/-- `d₄(W) = E_x ‖G_x(W) − Ā‖⁴`. -/
noncomputable def d4C (Abar : Fin n → ℝ) (W : J × Fin n → ℝ) : ℝ :=
  ∫ x, (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2 ∂D.ν

lemma PP_R4 (Abar : Fin n → ℝ) :
    PP ((2 + 2) + (2 + 2)) (fun x => (∑ i, (GpC D i x - C (Abar i)) ^ 2) ^ 2) :=
  (PP.sum Finset.univ fun i _ =>
    ((PP_GpC D i).sub ((PP_CcC (n := n) (J := J) (Abar i)).mono (by norm_num))).sq).sq

lemma int_d4 (Abar : Fin n → ℝ) : Integrable (d4C D Abar) (stdGauss (J × Fin n)) := by
  have := D.hν.prob
  have h := (PP_int_prod (PP_R4 D Abar) D.hν).integral_prod_right
  have e : d4C D Abar = fun W => ∫ x, (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2 ∂D.ν := rfl
  rw [e]
  simpa only [map_pow, map_sum, map_sub, eval_C, eval_GpC] using h

lemma d4C_nonneg (Abar : Fin n → ℝ) (W : J × Fin n → ℝ) : 0 ≤ d4C D Abar W :=
  integral_nonneg fun x => sq_nonneg _

lemma D4C_eq (Abar : Fin n → ℝ) :
    D4C D.ν D.ℓ D.H D.T D.mu D.ψ Abar = ∫ W, d4C D Abar W ∂stdGauss (J × Fin n) := rfl

/-- **The pointwise-in-`W` gradient bound** (steps 2–5). -/
lemma grad_pt (hH : D.H.IsSymm) (hT : SymT D.T) (Γ G4 : ℝ) (hΓ : 0 ≤ Γ) (hG4 : 0 ≤ G4)
    (hF : FeatOpA D.ν D.ψ Γ) (hF4 : Feat4A D.ν D.ψ G4) (Abar : Fin n → ℝ) (η : ℝ) (hη : 0 < η)
    (W : J × Fin n → ℝ) :
    ∑ α : J × Fin n, (eval W (pderiv α (PVC D))) ^ 2 ≤
      4 * ((1 + η) * nsq Abar * Γ * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W +
        (1 + 1 / η) * (G4 * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W *
          Real.sqrt (d4C D Abar W))) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [PVC_grad D hH hT, e, ← Finset.mul_sum]
  have hb := gradBound D.hν D.hψ Γ G4 hΓ hG4 hF hF4 (fun x => eval W (QpC D x))
    ((PP_QpC D).cont_x W) (fun i x => GvC D i x W) (fun i => cont_GvC D i W) Abar η hη
  refine (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (le_of_eq ?_)
  rw [PVC_eval' D W]
  rfl

/-- The variance bound for a bundled model. -/
theorem varBound_DC (hH : D.H.IsSymm) (hT : SymT D.T) (Γ G4 : ℝ) (hΓ : 0 ≤ Γ) (hG4 : 0 ≤ G4)
    (hF : FeatOpA D.ν D.ψ Γ) (hF4 : Feat4A D.ν D.ψ G4) (Abar : Fin n → ℝ) (η Dd s : ℝ)
    (hη : 0 < η) (hD : 0 ≤ Dd) (hs : 0 ≤ s)
    (hD4 : D4C D.ν D.ℓ D.H D.T D.mu D.ψ Abar ≤ Dd ^ 4)
    (hs2 : ∫ W, YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2 ∂stdGauss (J × Fin n) ≤ s ^ 2) :
    ∫ W, (YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W - YbC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ) ^ 2
        ∂stdGauss (J × Fin n) ≤
      4 * (1 + η) * nsq Abar * Γ * YbC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ +
        4 * (1 + 1 / η) * G4 * s * Dd ^ 2 := by
  have hpoin := BstLean.Part78.poincareMv (J × Fin n) (PVC D)
  simp only [PVC_eval] at hpoin
  have iY := (regC_D D).1
  have iY2 := (regC_D D).2
  have id4 := int_d4 D Abar
  have hc0 : 0 ≤ 4 * (1 + 1 / η) * G4 := by positivity
  refine opt _ _ _ s Dd _ _ hc0 hs hD hs2 hD4 fun t ht => ?_
  have k1 : Integrable (fun W => (4 * (1 + η) * nsq Abar * Γ) *
      YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W) (stdGauss (J × Fin n)) := iY.const_mul _
  have k3 : Integrable (fun W => (t / 2) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2)
      (stdGauss (J × Fin n)) := iY2.const_mul _
  have k4 : Integrable (fun W => (1 / (2 * t)) * d4C D Abar W) (stdGauss (J × Fin n)) :=
    id4.const_mul _
  have k34 : Integrable (fun W => (t / 2) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2 +
      (1 / (2 * t)) * d4C D Abar W) (stdGauss (J × Fin n)) := k3.add k4
  have k2 : Integrable (fun W => (4 * (1 + 1 / η) * G4) *
      ((t / 2) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2 +
      (1 / (2 * t)) * d4C D Abar W)) (stdGauss (J × Fin n)) := k34.const_mul _
  refine hpoin.trans ?_
  rw [← integral_finsetSum _ (fun α _ => gpi78 _ 2)]
  have e : 4 * (1 + η) * nsq Abar * Γ * YbC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ +
      4 * (1 + 1 / η) * G4 * ((t / 2) *
        (∫ W, YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2 ∂stdGauss (J × Fin n)) +
        (1 / (2 * t)) * D4C D.ν D.ℓ D.H D.T D.mu D.ψ Abar) =
      ∫ W, ((4 * (1 + η) * nsq Abar * Γ) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W +
        (4 * (1 + 1 / η) * G4) * ((t / 2) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2 +
          (1 / (2 * t)) * d4C D Abar W)) ∂stdGauss (J × Fin n) := by
    rw [integral_add k1 k2, integral_const_mul, integral_const_mul,
      integral_add k3 k4, integral_const_mul, integral_const_mul, D4C_eq, YbC]
  rw [e]
  refine integral_mono (integrable_finsetSum _ fun α _ => gpi78 _ 2)
    (k1.add k2) fun W => ?_
  refine (grad_pt D hH hT Γ G4 hΓ hG4 hF hF4 Abar η hη W).trans ?_
  have am := amgm t (YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W) (Real.sqrt (d4C D Abar W)) ht
  rw [Real.sq_sqrt (d4C_nonneg D Abar W)] at am
  have := mul_le_mul_of_nonneg_left am hc0
  show _ ≤ (4 * (1 + η) * nsq Abar * Γ) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W +
        (4 * (1 + 1 / η) * G4) * ((t / 2) * YC D.ν D.f0 D.ℓ D.H D.T D.mu D.ψ W ^ 2 +
          (1 / (2 * t)) * d4C D Abar W)
  linarith

/-- **The variance bound in one slice.** -/
theorem varBoundC : VarBoundC := by
  intro n J _ ν hν f0 ℓ H hH T hT mu ψ hmu hψ Γ G4 hΓ hG4 hF hF4 Abar η Dd s hη hD hs hD4 hs2
  exact varBound_DC ⟨ν, hν, f0, ℓ, H, T, mu, ψ, hmu, hψ⟩ hH hT Γ G4 hΓ hG4 hF hF4 Abar η Dd s
    hη hD hs hD4 hs2

end BstLean.Part90

#print axioms BstLean.Part90.regC
#print axioms BstLean.Part90.varBoundC
