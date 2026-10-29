import BstLean.Part89SDefs
import BstLean.Part89Gauss

/-!
# Part 89, the Gaussian model on a scale window

* `gmw_of`: `GMW M P lam (n Λ + 2) (n · cVW k (tS n β) Λ cV0 ϑ) Λ β` from the pointwise scale
  comparison `ScaleE` and a bound on the variance of `Vdn` at every scale of the window.
* `varAll89`: the variance of `Vdn` at every real scale, with the constant `104/100 Λ C_RH`.
* `intYbar_le_q`, `intYbar_nonneg`: `0 ≤ E_p Ȳ_p ≤ E_p q_p` at every real scale.
-/

namespace BstLean.Part89

open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open BstLean.Part29 (stdGauss)
open BstLean.Part84 (Fourth84 sq_shift_integral sq_integral_le var_le_sq)
open BstLean.Part86 BstLean.Part86.XGauss

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-! ## Real-variable facts -/

lemma sq_add_le89 (x y τ : ℝ) (hτ : 0 < τ) :
    (x + y) ^ 2 ≤ (1 + τ) * x ^ 2 + (1 + 1 / τ) * y ^ 2 := by
  have h1 : τ * (1 / τ) = 1 := mul_one_div_cancel hτ.ne'
  have h : (1 + τ) * x ^ 2 + (1 + 1 / τ) * y ^ 2 - (x + y) ^ 2 =
      (1 / τ) * (τ * x - y) ^ 2 := by
    have e : (1 / τ) * (τ * x - y) ^ 2 =
        (τ * (1 / τ)) * τ * x ^ 2 - 2 * (τ * (1 / τ)) * x * y + 1 / τ * y ^ 2 := by ring
    rw [e, h1]; ring
  have h0 : 0 ≤ (1 / τ) * (τ * x - y) ^ 2 :=
    mul_nonneg (one_div_nonneg.2 hτ.le) (sq_nonneg _)
  linarith

lemma tSc_nonneg (n : ℕ) (a b : ℝ) : 0 ≤ tSc n a b := by
  unfold tSc
  exact div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (le_min (sq_nonneg _) (sq_nonneg _))

lemma tSc_comm (n : ℕ) (a b : ℝ) : tSc n a b = tSc n b a := by
  unfold tSc; rw [abs_sub_comm, min_comm]

lemma a1S_nonneg (k : ℕ) (T : ℝ) (hT : 0 ≤ T) : 0 ≤ a1S k T := by
  unfold a1S
  have h1 : (1 : ℝ) ≤ 1 + k * T := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hT)
  have := one_le_pow₀ (n := 2 * k) h1
  linarith

lemma tauS_pos (k : ℕ) (T : ℝ) (hT : 0 < T) : 0 < tauS k T := by
  unfold tauS
  have h1 : (0 : ℝ) < 1 + k * T :=
    lt_of_lt_of_le one_pos (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hT.le))
  exact mul_pos hT (pow_pos h1 _)

lemma e1S_nonneg (k : ℕ) (T : ℝ) (hT : 0 < T) : 0 ≤ e1S k T := by
  unfold e1S
  have := a1S_nonneg k T hT.le
  have := (tauS_pos k T hT).le
  have := sq_nonneg (tauS k T)
  linarith

lemma e2S_eq (k : ℕ) (T Lam : ℝ) : e2S k T Lam = e1S k T + Lam * (2 + e1S k T) := by
  unfold e2S e1S; ring

/-- The drift of `q − v` between two scales, from the two-sided comparison of `q`. -/
lemma drift_real (q q' v v' e1 Lam : ℝ) (he : 0 ≤ e1) (hL : 0 ≤ Lam) (hq : 0 ≤ q)
    (hq' : 0 ≤ q') (h1 : q' ≤ (1 + e1) * q) (h2 : q ≤ (1 + e1) * q') (hv0 : 0 ≤ v)
    (hv : v ≤ Lam * q) (hv0' : 0 ≤ v') (hv' : v' ≤ Lam * q') :
    |(q' - v') - (q - v)| ≤ (e1 + Lam * (2 + e1)) * q := by
  have hLq : 0 ≤ Lam * q := mul_nonneg hL hq
  have hLeq : 0 ≤ Lam * (e1 * q) := mul_nonneg hL (mul_nonneg he hq)
  have hLq' : Lam * q' ≤ Lam * ((1 + e1) * q) := mul_le_mul_of_nonneg_left h1 hL
  have ex : (e1 + Lam * (2 + e1)) * q = e1 * q + 2 * (Lam * q) + Lam * (e1 * q) := by ring
  have ex2 : Lam * ((1 + e1) * q) = Lam * q + Lam * (e1 * q) := by ring
  have ex3 : (1 + e1) * q = q + e1 * q := by ring
  have ex4 : (1 + e1) * q' = q' + e1 * q' := by ring
  rw [ex]
  rw [ex2] at hLq'
  rw [ex3] at h1
  rw [ex4] at h2
  have heq : 0 ≤ e1 * q := mul_nonneg he hq
  rw [abs_le]
  constructor
  · rcases le_total q' q with h | h
    · have : e1 * q' ≤ e1 * q := mul_le_mul_of_nonneg_left h he
      linarith
    · linarith
  · linarith

/-! ## Comparison of the slice quantities between two scales -/

section cmp

variable (M : Mod n I J S G) [IsProbabilityMeasure M.pi] [IsProbabilityMeasure M.ga]
variable (hT : ∀ (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ),
  Tame (fun (W : J × Fin n → ℝ) (s : S × G) => Fs M P lam W s.1 s.2))

include hT

/-- `L` and `R` at the scale `b` from `L` and `R` at the scale `a`. -/
lemma slice_cmp (k : ℕ) (hE : ScaleE M k) (P : MvPolynomial (I ⊕ Fin n) ℝ)
    (hP : P.totalDegree ≤ k) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (T : ℝ) (hT0 : 0 < T)
    (htT : tSc n a b ≤ T) (p : S) :
    Lsl M P b p ≤ (1 + a1S k T) * Lsl M P a p ∧
    Rsl M P b p ≤ (1 + tauS k T) * Rsl M P a p +
      (tauS k T + tauS k T ^ 2) * Lsl M P a p := by
  have h0 : 0 ≤ tSc n a b := tSc_nonneg n a b
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb0 : (1 : ℝ) ≤ 1 + k * tSc n a b := le_add_of_nonneg_right (mul_nonneg hk0 h0)
  have hbT : 1 + k * tSc n a b ≤ 1 + k * T := by
    have := mul_le_mul_of_nonneg_left htT hk0
    linarith
  have hbT1 : (1 : ℝ) ≤ 1 + k * T := hb0.trans hbT
  have hA : (1 + k * tSc n a b) ^ (2 * k) ≤ 1 + a1S k T := by
    unfold a1S
    rw [add_sub_cancel]
    exact pow_le_pow_left₀ (by linarith) hbT _
  have hτ : 0 < tauS k T := tauS_pos k T hT0
  have hc : tSc n a b ^ 2 * (1 + k * tSc n a b) ^ k ≤ tauS k T ^ 2 := by
    unfold tauS
    rw [mul_pow, ← pow_mul]
    refine mul_le_mul (pow_le_pow_left₀ h0 htT 2) ?_ (pow_nonneg (by linarith) _)
      (pow_nonneg hT0.le _)
    calc (1 + k * tSc n a b) ^ k ≤ (1 + (k : ℝ) * T) ^ k :=
          pow_le_pow_left₀ (by linarith) hbT _
      _ ≤ (1 + (k : ℝ) * T) ^ (k * 2) := pow_le_pow_right₀ hbT1 (by omega)
  have hLa0 := Lsl_nonneg M P a hT p
  have iV : ∀ s : ℝ, Integrable (fun g =>
      ∫ W, (Fs M P s W p g - Phi M P s (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n)) M.ga :=
    fun s => ((((t_Fphi M P s hT).pow 2).intW).slice p).int_par M.ga
  have hLL : Lsl M P b p ≤ (1 + k * tSc n a b) ^ (2 * k) * Lsl M P a p := by
    have h := integral_mono (iV b) ((iV a).const_mul _)
      (fun g => (hE P hP a b ha hb (M.X (p, g))).2)
    rw [integral_const_mul] at h
    exact h
  refine ⟨hLL.trans (mul_le_mul_of_nonneg_right hA hLa0), ?_⟩
  have tPP := (t_Phi M P b hT).sub (t_Phi M P a hT)
  have iD : Integrable (fun g => (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) ^ 2)
      M.ga := ((tPP.pow 2).slice p).int_par M.ga
  have hD : ∫ g, (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) ^ 2 ∂M.ga ≤
      tSc n a b ^ 2 * (1 + k * tSc n a b) ^ k * Lsl M P a p := by
    have h := integral_mono iD ((iV a).const_mul _)
      (fun g => (hE P hP a b ha hb (M.X (p, g))).1)
    rw [integral_const_mul] at h
    exact h
  have hD2 : ∫ g, (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) ^ 2 ∂M.ga ≤
      tauS k T ^ 2 * Lsl M P a p := hD.trans (mul_le_mul_of_nonneg_right hc hLa0)
  have tb := (t_mbar M P a hT).comp_right (measurable_fst : Measurable (Prod.fst : S × G → S))
  have iPb : Integrable (fun g => Phi M P b (M.X (p, g))) M.ga :=
    ((t_Phi M P b hT).slice p).int_par M.ga
  have iPb2 : Integrable (fun g => Phi M P b (M.X (p, g)) ^ 2) M.ga :=
    (((t_Phi M P b hT).pow 2).slice p).int_par M.ga
  have hs : ∫ g, (Phi M P b (M.X (p, g)) - mbar M P a p) ^ 2 ∂M.ga =
      ∫ g, (Phi M P b (M.X (p, g)) - ∫ y, Phi M P b (M.X (p, y)) ∂M.ga) ^ 2 ∂M.ga +
        (∫ y, Phi M P b (M.X (p, y)) ∂M.ga - mbar M P a p) ^ 2 :=
    var_shift M.ga (fun g => Phi M P b (M.X (p, g))) iPb iPb2 (mbar M P a p)
  rw [← mbar_eq M P b hT p] at hs
  have hRb : Rsl M P b p = ∫ g, (Phi M P b (M.X (p, g)) - mbar M P b p) ^ 2 ∂M.ga := rfl
  have hR1 : Rsl M P b p ≤ ∫ g, (Phi M P b (M.X (p, g)) - mbar M P a p) ^ 2 ∂M.ga := by
    rw [hRb, hs]
    have := sq_nonneg (mbar M P b p - mbar M P a p)
    linarith
  have iA : Integrable (fun g => (Phi M P b (M.X (p, g)) - mbar M P a p) ^ 2) M.ga :=
    ((((t_Phi M P b hT).sub tb).pow 2).slice p).int_par M.ga
  have iRa : Integrable (fun g => (Phi M P a (M.X (p, g)) - mbar M P a p) ^ 2) M.ga :=
    ((((t_Phi M P a hT).sub tb).pow 2).slice p).int_par M.ga
  have hpt : ∀ g, (Phi M P b (M.X (p, g)) - mbar M P a p) ^ 2 ≤
      (1 + tauS k T) * (Phi M P a (M.X (p, g)) - mbar M P a p) ^ 2 +
      (1 + 1 / tauS k T) * (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) ^ 2 := by
    intro g
    have h := sq_add_le89 (Phi M P a (M.X (p, g)) - mbar M P a p)
      (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) (tauS k T) hτ
    have e : Phi M P a (M.X (p, g)) - mbar M P a p +
        (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) =
        Phi M P b (M.X (p, g)) - mbar M P a p := by ring
    rw [e] at h
    exact h
  have h2 : ∫ g, (Phi M P b (M.X (p, g)) - mbar M P a p) ^ 2 ∂M.ga ≤
      ∫ g, ((1 + tauS k T) * (Phi M P a (M.X (p, g)) - mbar M P a p) ^ 2 +
        (1 + 1 / tauS k T) * (Phi M P b (M.X (p, g)) - Phi M P a (M.X (p, g))) ^ 2) ∂M.ga :=
    integral_mono iA ((iRa.const_mul _).add (iD.const_mul _)) hpt
  rw [integral_add (iRa.const_mul _) (iD.const_mul _), integral_const_mul,
    integral_const_mul] at h2
  have hRa : ∫ g, (Phi M P a (M.X (p, g)) - mbar M P a p) ^ 2 ∂M.ga = Rsl M P a p := rfl
  rw [hRa] at h2
  have hc1 : 0 ≤ 1 + 1 / tauS k T := by
    have := one_div_nonneg.2 hτ.le
    linarith
  have h3 := mul_le_mul_of_nonneg_left hD2 hc1
  have e : (1 + 1 / tauS k T) * (tauS k T ^ 2 * Lsl M P a p) =
      (tauS k T + tauS k T ^ 2) * Lsl M P a p := by
    have h1 : tauS k T * (1 / tauS k T) = 1 := mul_one_div_cancel hτ.ne'
    calc (1 + 1 / tauS k T) * (tauS k T ^ 2 * Lsl M P a p)
        = (tauS k T ^ 2 + tauS k T * (tauS k T * (1 / tauS k T))) * Lsl M P a p := by ring
      _ = (tauS k T + tauS k T ^ 2) * Lsl M P a p := by rw [h1]; ring
  rw [e] at h3
  linarith

/-- `q` at the scale `b` from `q` at the scale `a`. -/
lemma q_cmp (k : ℕ) (hE : ScaleE M k) (P : MvPolynomial (I ⊕ Fin n) ℝ)
    (hP : P.totalDegree ≤ k) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (T : ℝ) (hT0 : 0 < T)
    (htT : tSc n a b ≤ T) (p : S) :
    qsl M P b p ≤ (1 + e1S k T) * qsl M P a p := by
  obtain ⟨h1, h2⟩ := slice_cmp M hT k hE P hP a b ha hb T hT0 htT p
  rw [q_split M P b hT p, q_split M P a hT p]
  have hL0 := Lsl_nonneg M P a hT p
  have hR0 := Rsl_nonneg M P a p
  have ha1 := a1S_nonneg k T hT0.le
  have hx : 0 ≤ (a1S k T + tauS k T ^ 2) * Rsl M P a p :=
    mul_nonneg (add_nonneg ha1 (sq_nonneg _)) hR0
  have e : (1 + e1S k T) * (Lsl M P a p + Rsl M P a p) =
      (1 + a1S k T) * Lsl M P a p + ((1 + tauS k T) * Rsl M P a p +
        (tauS k T + tauS k T ^ 2) * Lsl M P a p) +
        (a1S k T + tauS k T ^ 2) * Rsl M P a p := by
    unfold e1S; ring
  rw [e]
  linarith

end cmp

/-! ## The exports at every scale -/

/-- `0 ≤ E_p Ȳ_p`. -/
theorem intYbar_nonneg (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    0 ≤ ∫ p, Ybar M P lam p ∂M.pi :=
  integral_nonneg fun p => Ybar_nonneg M P lam p

/-- `E_p Ȳ_p ≤ E_p q_p`. -/
theorem intYbar_le_q (M : Mod n I J S G) (d : ℕ) (hR : Reg M d) (hPF : PolyFacts M d)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    ∫ p, Ybar M P lam p ∂M.pi ≤ ∫ p, qsl M P lam p ∂M.pi := by
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have iq : Integrable (fun p => qsl M P lam p) M.pi := (t_q M P lam hT).int_par M.pi
  have iv : Integrable (fun p => vsl M P lam p) M.pi := (t_v M P lam hT).int_par M.pi
  have iY : Integrable (fun p => Ybar M P lam p) M.pi :=
    (iq.sub iv).congr (Filter.Eventually.of_forall fun p => (Ybar_eq M P lam hT p).symm)
  refine integral_mono iY iq fun p => ?_
  have := v_nonneg M P lam p
  show Ybar M P lam p ≤ qsl M P lam p
  rw [Ybar_eq M P lam hT p]
  linarith

/-- **The variance of `Vdn` at every real scale**, with the constant of `VY_le89`. -/
theorem varAll89 (M : Mod n I J S G) (d k : ℕ) (Lam CRH K4 : ℝ) (hn : 2 ≤ n)
    (hR : Reg M d) (hPF : PolyFacts M d) (hD : Decor86 M Lam)
    (hRH : SliceRH M (d * k) CRH) (h4 : Fourth84 k K4)
    (hL : 0 ≤ Lam) (hLC : Lam * CRH ≤ 1 / 100) (hK : 10000 * (K4 * Lam) ≤ CRH) (hK0 : 0 ≤ K4)
    (hC0 : 0 ≤ CRH) (P : MvPolynomial (I ⊕ Fin n) ℝ) (hP : P.totalDegree ≤ k) (lam : ℝ) :
    ∫ W, (Vdn M P lam W - ∫ p, Ybar M P lam p ∂M.pi) ^ 2 ∂stdGauss (J × Fin n) ≤
      104 / 100 * (Lam * CRH) * (∫ p, qsl M P lam p ∂M.pi) ^ 2 := by
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have hPFk := hPF k P hP
  have hpoly : ∀ W : J × Fin n → ℝ, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ d * k ∧
      ∀ x, MvPolynomial.eval x Q = Fm M P lam W x := fun W => hPFk.1 lam W
  have hpolyW : ∀ p : S, ∃ Q : MvPolynomial (J × Fin n) ℝ, Q.totalDegree ≤ k ∧
      ∀ W, MvPolynomial.eval W Q = msl M P lam W p := fun p => hPFk.2.2.1 lam p
  have tq := t_q M P lam hT
  have tv := t_v M P lam hT
  have tY := t_Y M P lam hT
  have iq : Integrable (fun p => qsl M P lam p) M.pi := tq.int_par M.pi
  have iv : Integrable (fun p => vsl M P lam p) M.pi := tv.int_par M.pi
  have hYb : ∫ p, Ybar M P lam p ∂M.pi = ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => Ybar_eq M P lam hT p)
  rw [hYb]
  have th : Tame (fun (W : J × Fin n → ℝ) (p : S) =>
      Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) := tY.sub (tq.sub tv)
  have tH : Tame (fun (W : J × Fin n → ℝ) (z : S × S) =>
      (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
      (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2))) :=
    (th.comp_right measurable_fst).mul (th.comp_right measurable_snd)
  have e1 : ∀ W, (Vdn M P lam W - ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi) ^ 2 =
      ∫ z, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
        (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂(M.pi.prod M.pi) := by
    intro W
    have a : Vdn M P lam W - ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi =
        ∫ p, (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ∂M.pi :=
      (integral_sub (tY.int_right W M.pi) (iq.sub iv)).symm
    have b := integral_prod_mul (μ := M.pi) (ν := M.pi)
      (fun p => Ysl M P lam W p - (qsl M P lam p - vsl M P lam p))
      (fun p => Ysl M P lam W p - (qsl M P lam p - vsl M P lam p))
    rw [a, sq]; exact b.symm
  simp only [e1]
  rw [tH.swap (M.pi.prod M.pi)]
  have hc0 : 0 ≤ 104 / 100 * (Lam * CRH) := by positivity
  have hpt : ∀ z : S × S, ∫ W, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
        (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂stdGauss (J × Fin n) ≤
      104 / 100 * (Lam * CRH) * (qsl M P lam z.1 * qsl M P lam z.2) := by
    intro z
    have hcs := cs_sq (stdGauss (J × Fin n))
      (fun W => Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1))
      (fun W => Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2))
      ((th.pow 2).int_left z.1) ((th.pow 2).int_left z.2) (tH.int_left z)
    have hA := VY_le89 M P lam hT Lam CRH K4 (d * k) k hD hRH h4 hL hC0 hLC hK hK0 hpoly z.1
      (hpolyW z.1)
    have hB := VY_le89 M P lam hT Lam CRH K4 (d * k) k hD hRH h4 hL hC0 hLC hK hK0 hpoly z.2
      (hpolyW z.2)
    have hq1 := q_nonneg M P lam hT z.1
    have hq2 := q_nonneg M P lam hT z.2
    have hX : 0 ≤ 104 / 100 * (Lam * CRH) * (qsl M P lam z.1 * qsl M P lam z.2) := by positivity
    have hprod := mul_le_mul hA hB (integral_nonneg fun W => sq_nonneg _)
      (by positivity : 0 ≤ 104 / 100 * (Lam * CRH) * qsl M P lam z.1 ^ 2)
    have hsq : (∫ W, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
        (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂stdGauss (J × Fin n)) ^ 2 ≤
        (104 / 100 * (Lam * CRH) * (qsl M P lam z.1 * qsl M P lam z.2)) ^ 2 := by
      refine (hcs.trans hprod).trans (le_of_eq ?_); ring
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hX)
  have iR : Integrable (fun z : S × S => qsl M P lam z.1 * qsl M P lam z.2)
      (M.pi.prod M.pi) :=
    ((tq.comp_right measurable_fst).mul (tq.comp_right measurable_snd)).int_par
      (M.pi.prod M.pi)
  have h1 := integral_mono (tH.intW.int_par (M.pi.prod M.pi)) (iR.const_mul _) hpt
  rw [integral_const_mul, integral_prod_mul (μ := M.pi) (ν := M.pi)
    (fun p => qsl M P lam p) (fun p => qsl M P lam p)] at h1
  rw [sq]; exact h1

/-! ## The Gaussian model on the window -/

/-- **The Gaussian model on a scale window** from the scale comparison and a variance bound at
every scale of the window. -/
theorem gmw_of (M : Mod n I J S G) (d k : ℕ) (Lam cV0 β ϑ : ℝ) (hn : 2 ≤ n)
    (hR : Reg M d) (hPF : PolyFacts M d) (hD : Decor86 M Lam) (hSc : Scale86 M k)
    (hE : ScaleE M k) (hL : 0 ≤ Lam) (hL1 : Lam ≤ 1) (hcV0 : 0 ≤ cV0)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (hP : P.totalDegree ≤ k) (lam : ℝ)
    (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ))
    (hV : ∀ u : ℝ, 1 - β ≤ u → u ≤ 1 + β →
      ∫ W, (Vdn M P (|lam| * Real.sqrt u) W - ∫ p, Ybar M P (|lam| * Real.sqrt u) p ∂M.pi) ^ 2
          ∂stdGauss (J × Fin n) ≤
        cV0 * (∫ p, qsl M P (|lam| * Real.sqrt u) p ∂M.pi) ^ 2) :
    GMW M P lam (n * Lam + 2) (n * cVW k (tS n β) Lam cV0 ϑ) Lam β := by
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have tq := t_q M P lam hT
  have tv := t_v M P lam hT
  have tL := t_L M P lam hT
  have tm := t_msl M P lam hT
  have tg := t_gsl M P hT
  have iq : Integrable (fun p => qsl M P lam p) M.pi := tq.int_par M.pi
  have iv : Integrable (fun p => vsl M P lam p) M.pi := tv.int_par M.pi
  have iL : Integrable (fun p => Lsl M P lam p) M.pi := tL.int_par M.pi
  have iYs : ∀ s : ℝ, Integrable (fun p => Ybar M P s p) M.pi := fun s =>
    (((t_q M P s hT).int_par M.pi).sub ((t_v M P s hT).int_par M.pi)).congr
      (Filter.Eventually.of_forall fun p => (Ybar_eq M P s hT p).symm)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h] at hlam
    have e : |((0 : ℝ)) ^ 2 - 1| = 1 := by norm_num
    rw [e] at hlam
    have h1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
    linarith
  have hsq : 0 < lam ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hlam0))
  have hLv0 : 0 ≤ ∫ p, qsl M P lam p ∂M.pi := integral_nonneg (q_nonneg M P lam hT)
  have hvqs : ∀ (s : ℝ) (p : S), vsl M P s p ≤ Lam * qsl M P s p := fun s p =>
    (hD P s p).trans (mul_le_mul_of_nonneg_left (L_le_q M P s hT p) hL)
  have hvq := hvqs lam
  have tE : Tame (fun (W : J × Fin n → ℝ) (p : S) => (msl M P lam W p - gsl M P p) ^ 2) :=
    (tm.sub tg).pow 2
  have hYb : ∫ p, Ybar M P lam p ∂M.pi = ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => Ybar_eq M P lam hT p)
  have hT0 : 0 < tS n β := by
    unfold tS
    exact div_pos (mul_pos hβ0 (Real.sqrt_pos.2 (by linarith))) (by linarith)
  refine ⟨∫ p, qsl M P lam p ∂M.pi, ∫ p, Ybar M P lam p ∂M.pi, hLv0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hYb, ← integral_const_mul]
    exact integral_mono (iq.const_mul _) (iq.sub iv) (fun p => by
      have := hvq p
      show (1 - Lam) * qsl M P lam p ≤ qsl M P lam p - vsl M P lam p
      linarith)
  · exact (tE.intAll M.pi).int_left ()
  · have sw : ∫ W, Esl M P lam W ∂stdGauss (J × Fin n) =
        ∫ p, ∫ W, (msl M P lam W p - gsl M P p) ^ 2 ∂stdGauss (J × Fin n) ∂M.pi := tE.swap M.pi
    rw [sw]
    have hc : 0 ≤ Lam + 2 / (n : ℝ) := by positivity
    have h1 : ∫ p, ∫ W, (msl M P lam W p - gsl M P p) ^ 2 ∂stdGauss (J × Fin n) ∂M.pi ≤
        ∫ p, (Lam + 2 / (n : ℝ)) * Lsl M P lam p ∂M.pi :=
      integral_mono (tE.intW.int_par M.pi) (iL.const_mul _)
        (fun p => E_le M P lam hT Lam k hD hSc hP hlam p)
    rw [integral_const_mul] at h1
    have h2 : ∫ p, Lsl M P lam p ∂M.pi ≤ ∫ p, qsl M P lam p ∂M.pi :=
      integral_mono iL iq (L_le_q M P lam hT)
    have e : ((n : ℝ) * Lam + 2) / n = Lam + 2 / (n : ℝ) := by field_simp
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)
  · have tR : Tame (ι := J × Fin n) (fun _ (s : S × G) =>
        (Phi M P 1 (M.X s) - gsl M P s.1) ^ 2) :=
      ((t_Phi M P 1 hT).sub (tg.comp_right measurable_fst)).pow 2
    have h1 : R1 M P ≤ ∫ p, 2 * qsl M P lam p ∂M.pi :=
      integral_mono ((tR.intR M.ga).int_par M.pi) (iq.const_mul 2)
        (fun p => R_le M P lam hT k hSc hn hP hlam p)
    rw [integral_const_mul] at h1
    exact h1
  · intro u hu1 hu2
    have hu0 : 0 < u := by linarith
    have hV' := hV u hu1 hu2
    have hl'0 : |lam| * Real.sqrt u ≠ 0 :=
      mul_ne_zero (abs_ne_zero.2 hlam0) (Real.sqrt_ne_zero'.2 hu0)
    have hl'2 : (|lam| * Real.sqrt u) ^ 2 = lam ^ 2 * u := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hu0.le]
    have htT : tSc n lam (|lam| * Real.sqrt u) ≤ tS n β := by
      unfold tSc tS
      rw [hl'2]
      have hm : lam ^ 2 * (1 - β) ≤ min (lam ^ 2) (lam ^ 2 * u) :=
        le_min (by nlinarith) (mul_le_mul_of_nonneg_left hu1 hsq.le)
      have hm0 : 0 < min (lam ^ 2) (lam ^ 2 * u) :=
        lt_of_lt_of_le (mul_pos hsq (by linarith)) hm
      rw [div_le_div_iff₀ hm0 (by linarith)]
      have habs : |lam ^ 2 * u - lam ^ 2| ≤ lam ^ 2 * β := by
        have e : lam ^ 2 * u - lam ^ 2 = lam ^ 2 * (u - 1) := by ring
        rw [e, abs_mul, abs_of_pos hsq]
        exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hsq.le
      have hs := Real.sqrt_nonneg (n : ℝ)
      calc |lam ^ 2 * u - lam ^ 2| * Real.sqrt n * (1 - β)
          ≤ lam ^ 2 * β * Real.sqrt n * (1 - β) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hs) (by linarith)
        _ = β * Real.sqrt n * (lam ^ 2 * (1 - β)) := by ring
        _ ≤ β * Real.sqrt n * min (lam ^ 2) (lam ^ 2 * u) :=
            mul_le_mul_of_nonneg_left hm (mul_nonneg hβ0.le hs)
    have htT' : tSc n (|lam| * Real.sqrt u) lam ≤ tS n β := by rw [tSc_comm]; exact htT
    generalize |lam| * Real.sqrt u = lam' at hV' hl'0 htT htT' ⊢
    have he1 := e1S_nonneg k (tS n β) hT0
    have hq1 : ∀ p, qsl M P lam' p ≤ (1 + e1S k (tS n β)) * qsl M P lam p := fun p =>
      q_cmp M hT k hE P hP lam lam' hlam0 hl'0 _ hT0 htT p
    have hq2 : ∀ p, qsl M P lam p ≤ (1 + e1S k (tS n β)) * qsl M P lam' p := fun p =>
      q_cmp M hT k hE P hP lam' lam hl'0 hlam0 _ hT0 htT' p
    have hdr : ∀ p, |Ybar M P lam' p - Ybar M P lam p| ≤
        e2S k (tS n β) Lam * qsl M P lam p := by
      intro p
      rw [Ybar_eq M P lam' hT p, Ybar_eq M P lam hT p, e2S_eq]
      exact drift_real _ _ _ _ _ _ he1 hL (q_nonneg M P lam hT p) (q_nonneg M P lam' hT p)
        (hq1 p) (hq2 p) (v_nonneg M P lam p) (hvq p) (v_nonneg M P lam' p) (hvqs lam' p)
    have iq' : Integrable (fun p => qsl M P lam' p) M.pi := (t_q M P lam' hT).int_par M.pi
    have hLv'0 : 0 ≤ ∫ p, qsl M P lam' p ∂M.pi := integral_nonneg (q_nonneg M P lam' hT)
    have hLv' : ∫ p, qsl M P lam' p ∂M.pi ≤
        (1 + e1S k (tS n β)) * ∫ p, qsl M P lam p ∂M.pi := by
      have h := integral_mono iq' (iq.const_mul _) hq1
      rw [integral_const_mul] at h
      exact h
    have hdrI : |∫ p, Ybar M P lam' p ∂M.pi - ∫ p, Ybar M P lam p ∂M.pi| ≤
        e2S k (tS n β) Lam * ∫ p, qsl M P lam p ∂M.pi := by
      rw [← integral_sub (iYs lam') (iYs lam)]
      calc |∫ p, (Ybar M P lam' p - Ybar M P lam p) ∂M.pi|
          ≤ ∫ p, |Ybar M P lam' p - Ybar M P lam p| ∂M.pi := abs_integral_le_integral_abs
        _ ≤ ∫ p, e2S k (tS n β) Lam * qsl M P lam p ∂M.pi :=
            integral_mono ((iYs lam').sub (iYs lam)).abs (iq.const_mul _) hdr
        _ = e2S k (tS n β) Lam * ∫ p, qsl M P lam p ∂M.pi := integral_const_mul _ _
    have tVd : Tame (fun (W : J × Fin n → ℝ) (_ : Unit) => Vdn M P lam' W) :=
      (t_Y M P lam' hT).intAll M.pi
    have iA : ∀ c : ℝ, Integrable (fun W : J × Fin n → ℝ => (Vdn M P lam' W - c) ^ 2)
        (stdGauss (J × Fin n)) := fun c => ((tVd.sub (Tame.const c)).pow 2).int_left ()
    refine ⟨iA _, ?_⟩
    set Lv := ∫ p, qsl M P lam p ∂M.pi with hLv
    set Lv' := ∫ p, qsl M P lam' p ∂M.pi with hLv'd
    set Vb := ∫ p, Ybar M P lam p ∂M.pi with hVb
    set Yb' := ∫ p, Ybar M P lam' p ∂M.pi with hYb'
    have hpt : ∀ W : J × Fin n → ℝ, (Vdn M P lam' W - Vb) ^ 2 ≤
        (1 + ϑ) * (Vdn M P lam' W - Yb') ^ 2 + (1 + 1 / ϑ) * (Yb' - Vb) ^ 2 := by
      intro W
      have h := sq_add_le89 (Vdn M P lam' W - Yb') (Yb' - Vb) ϑ hϑ
      have e : Vdn M P lam' W - Yb' + (Yb' - Vb) = Vdn M P lam' W - Vb := by ring
      rw [e] at h
      exact h
    have h1 : ∫ W, (Vdn M P lam' W - Vb) ^ 2 ∂stdGauss (J × Fin n) ≤
        ∫ W, ((1 + ϑ) * (Vdn M P lam' W - Yb') ^ 2 + (1 + 1 / ϑ) * (Yb' - Vb) ^ 2)
          ∂stdGauss (J × Fin n) :=
      integral_mono (iA Vb) (((iA Yb').const_mul (1 + ϑ)).add
        (integrable_const ((1 + 1 / ϑ) * (Yb' - Vb) ^ 2))) hpt
    rw [integral_add ((iA Yb').const_mul (1 + ϑ)) (integrable_const _), integral_const_mul,
      integral_const] at h1
    simp only [probReal_univ, smul_eq_mul, one_mul] at h1
    have hϑ1 : 0 ≤ 1 + ϑ := by linarith
    have hϑ2 : 0 ≤ 1 + 1 / ϑ := by
      have := one_div_nonneg.2 hϑ.le
      linarith
    have hA : (1 + ϑ) * ∫ W, (Vdn M P lam' W - Yb') ^ 2 ∂stdGauss (J × Fin n) ≤
        (1 + ϑ) * (cV0 * ((1 + e1S k (tS n β)) * Lv) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hV'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLv'0 hLv' 2) hcV0)) hϑ1
    have hB : (1 + 1 / ϑ) * (Yb' - Vb) ^ 2 ≤
        (1 + 1 / ϑ) * (e2S k (tS n β) Lam * Lv) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hϑ2
      rw [← sq_abs (Yb' - Vb)]
      exact pow_le_pow_left₀ (abs_nonneg _) hdrI 2
    have e : (n : ℝ) * cVW k (tS n β) Lam cV0 ϑ / n * Lv ^ 2 =
        (1 + ϑ) * (cV0 * ((1 + e1S k (tS n β)) * Lv) ^ 2) +
          (1 + 1 / ϑ) * (e2S k (tS n β) Lam * Lv) ^ 2 := by
      rw [mul_div_cancel_left₀ _ hn0]
      unfold cVW; ring
    rw [e]
    linarith

end BstLean.Part89

#print axioms BstLean.Part89.gmw_of
#print axioms BstLean.Part89.varAll89
#print axioms BstLean.Part89.intYbar_le_q
#print axioms BstLean.Part89.intYbar_nonneg
