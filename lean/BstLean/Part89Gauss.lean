import BstLean.Part86Gauss
import BstLean.Part89Defs

/-!
# Part 89, the Gaussian model given the anchors with sharper constants

* `gaussModel89`: `GaussModel86 M k (n Λ + 2) ((104/100) n Λ C_RH) Λ` under `Λ C_RH ≤ 1/100` and
  `10000 K4 Λ ≤ C_RH`.
* `gaussModelV`: the model for one polynomial from an abstract bound on the variance of `Vdn`.
-/

namespace BstLean.Part89

open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open BstLean.Part29 (stdGauss)
open BstLean.Part84 (Fourth84 sq_shift_integral sq_integral_le var_le_sq)
open BstLean.Part86 BstLean.Part86.XGauss

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-- `Ȳ_p = E_W Y_p`. -/
noncomputable def Ybar (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) (p : S) : ℝ :=
  ∫ W, Ysl M P lam W p ∂stdGauss (J × Fin n)

lemma Ybar_nonneg (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) (p : S) :
    0 ≤ Ybar M P lam p :=
  integral_nonneg fun W => integral_nonneg fun g => sq_nonneg _

section slices

variable (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ)
variable [IsProbabilityMeasure M.pi] [IsProbabilityMeasure M.ga]
variable (hT : ∀ (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ),
  Tame (fun (W : J × Fin n → ℝ) (s : S × G) => Fs M P lam W s.1 s.2))

include hT

lemma Ybar_eq (p : S) : Ybar M P lam p = qsl M P lam p - vsl M P lam p := by
  have tQ := t_Qf M P lam hT
  have te := t_et M P lam hT
  unfold Ybar
  simp only [Ysl_eq M P lam hT]
  rw [integral_sub (tQ.int_left p) ((te.pow 2).int_left p)]
  rfl

/-- The variance of `Q_p`, with the constant `100/99`. -/
lemma VQ_le89 (Lam CRH : ℝ) (D : ℕ) (hD : Decor86 M Lam) (hRH : SliceRH M D CRH)
    (hL : 0 ≤ Lam) (hC0 : 0 ≤ CRH) (hLC : Lam * CRH ≤ 1 / 100)
    (hpoly : ∀ W : J × Fin n → ℝ, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ D ∧
      ∀ x, MvPolynomial.eval x Q = Fm M P lam W x) (p : S) :
    ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤
      100 / 99 * (Lam * CRH) * qsl M P lam p ^ 2 := by
  have tFc := t_Fc M P lam hT
  have e0 : ∀ (W : J × Fin n → ℝ) (x : Fin n → ℝ),
      Fm M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam W x =
        (Fm M P lam W x - mbar M P lam p) ^ 2 := by
    intro W x; unfold Fm; rw [map_pow, map_sub, MvPolynomial.eval_C]
  have hm : ∀ W, msl M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam W p = Qf M P lam W p := by
    intro W; unfold msl Qf Fs; simp only [e0]
  have hphi : ∀ g, Phi M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam (M.X (p, g)) =
      ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n) := by
    intro g; unfold Phi Fs; simp only [e0]
  have hfs : ∀ W g, Fs M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam W p g =
      (Fs M P lam W p g - mbar M P lam p) ^ 2 := fun W g => e0 W _
  have h := hD ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam p
  simp only [hm, hphi, hfs] at h
  have hA : ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤
      Lam * ∫ g, ∫ W, ((Fs M P lam W p g - mbar M P lam p) ^ 2 -
        ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) ∂M.ga := h
  have h2 : ∀ g, ∫ W, ((Fs M P lam W p g - mbar M P lam p) ^ 2 -
        ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) ≤
      ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) := by
    intro g
    have := var_le_sq (stdGauss (J × Fin n)) (fun W => (Fs M P lam W p g - mbar M P lam p) ^ 2)
      ((tFc.pow 2).int_left (p, g)) (((tFc.pow 2).pow 2).int_left (p, g))
    refine this.trans (le_of_eq ?_)
    congr 1; funext W; ring
  have i1 : Integrable (fun g => ∫ W, ((Fs M P lam W p g - mbar M P lam p) ^ 2 -
        ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n)) M.ga :=
    (((((tFc.pow 2).sub ((tFc.pow 2).intW)).pow 2).intW).slice p).int_par M.ga
  have i2 : Integrable (fun g =>
      ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n)) M.ga :=
    (((tFc.pow 4).intW).slice p).int_par M.ga
  have hB := integral_mono i1 i2 h2
  have hsw : ∫ g, ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) ∂M.ga =
      ∫ W, ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂M.ga ∂stdGauss (J × Fin n) :=
    (((tFc.pow 4).slice p).swap M.ga).symm
  have h3 : ∀ W, ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂M.ga ≤
      CRH * Qf M P lam W p ^ 2 := by
    intro W
    obtain ⟨Q0, hdeg, hev⟩ := hpoly W
    have := hRH p (Q0 - MvPolynomial.C (mbar M P lam p))
      ((MvPolynomial.totalDegree_sub_C_le Q0 _).trans hdeg)
    simp only [map_sub, MvPolynomial.eval_C, hev] at this
    exact this
  have i3 : Integrable (fun W => ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂M.ga)
      (stdGauss (J × Fin n)) := ((tFc.pow 4).intR M.ga).int_left p
  have tQ := t_Qf M P lam hT
  have i4 : Integrable (fun W => Qf M P lam W p ^ 2) (stdGauss (J × Fin n)) :=
    (tQ.pow 2).int_left p
  have hC := integral_mono i3 (i4.const_mul CRH) h3
  rw [integral_const_mul] at hC
  have hS := (sq_shift_integral (stdGauss (J × Fin n)) (fun W => Qf M P lam W p)
    (tQ.int_left p) i4 (qsl M P lam p)).2
  have hq : ∫ W, Qf M P lam W p ∂stdGauss (J × Fin n) = qsl M P lam p := rfl
  rw [hq] at hS
  have hV0 : 0 ≤ ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) :=
    integral_nonneg fun W => sq_nonneg _
  set VQ := ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n)
  set S2 := ∫ W, Qf M P lam W p ^ 2 ∂stdGauss (J × Fin n)
  set I4 := ∫ g, ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) ∂M.ga
  have hI : I4 ≤ CRH * S2 := by rw [hsw]; exact hC
  have hVI : VQ ≤ Lam * I4 := hA.trans (mul_le_mul_of_nonneg_left hB hL)
  have hS2 : S2 = VQ + qsl M P lam p ^ 2 := by rw [hS]; ring
  have h5 : VQ ≤ Lam * CRH * (VQ + qsl M P lam p ^ 2) := by
    calc VQ ≤ Lam * I4 := hVI
      _ ≤ Lam * (CRH * S2) := mul_le_mul_of_nonneg_left hI hL
      _ = Lam * CRH * (VQ + qsl M P lam p ^ 2) := by rw [hS2]; ring
  have ha0 : 0 ≤ Lam * CRH := mul_nonneg hL hC0
  have hx1 := mul_nonneg hV0 (by linarith : (0 : ℝ) ≤ 1 / 100 - Lam * CRH)
  have hx2 := mul_nonneg ha0 (sq_nonneg (qsl M P lam p))
  set x := Lam * CRH
  set q2 := qsl M P lam p ^ 2
  have h6 : VQ ≤ x * VQ + x * q2 := by rw [← mul_add]; exact h5
  have h7 : 0 ≤ VQ * (1 / 100) - VQ * x := by rw [← mul_sub]; exact hx1
  have h8 : 100 / 99 * x * q2 = 100 / 99 * (x * q2) := by ring
  rw [h8]
  linarith [mul_comm VQ x]

/-- The variance of `Y_p`, with the constant `104/100`. -/
lemma VY_le89 (Lam CRH K4 : ℝ) (D k : ℕ) (hD : Decor86 M Lam) (hRH : SliceRH M D CRH)
    (h4 : Fourth84 k K4) (hL : 0 ≤ Lam) (hC0 : 0 ≤ CRH) (hLC : Lam * CRH ≤ 1 / 100)
    (hK : 10000 * (K4 * Lam) ≤ CRH) (hK0 : 0 ≤ K4)
    (hpoly : ∀ W : J × Fin n → ℝ, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ D ∧
      ∀ x, MvPolynomial.eval x Q = Fm M P lam W x) (p : S)
    (hpolyW : ∃ Q : MvPolynomial (J × Fin n) ℝ, Q.totalDegree ≤ k ∧
      ∀ W, MvPolynomial.eval W Q = msl M P lam W p) :
    ∫ W, (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2 ∂stdGauss (J × Fin n) ≤
      104 / 100 * (Lam * CRH) * qsl M P lam p ^ 2 := by
  have hVQ := VQ_le89 M P lam hT Lam CRH D hD hRH hL hC0 hLC hpoly p
  have tQ := t_Qf M P lam hT
  have tq := t_q M P lam hT
  have tv := t_v M P lam hT
  have te := t_et M P lam hT
  have tY := t_Y M P lam hT
  have iL : Integrable (fun W => (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2)
      (stdGauss (J × Fin n)) := ((tY.sub (tq.sub tv)).pow 2).int_left p
  have iQ : Integrable (fun W => (Qf M P lam W p - qsl M P lam p) ^ 2)
      (stdGauss (J × Fin n)) := ((tQ.sub tq).pow 2).int_left p
  have iE : Integrable (fun W => ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2)
      (stdGauss (J × Fin n)) := (((te.pow 2).sub tv).pow 2).int_left p
  have h1 : ∫ W, (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2
        ∂stdGauss (J × Fin n) ≤
      ∫ W, (100 / 99 * (Qf M P lam W p - qsl M P lam p) ^ 2 +
        100 * ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2)
        ∂stdGauss (J × Fin n) := by
    refine integral_mono iL ((iQ.const_mul _).add (iE.const_mul _)) (fun W => ?_)
    show (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2 ≤ _
    rw [Ysl_eq M P lam hT W p]
    nlinarith [sq_nonneg ((Qf M P lam W p - qsl M P lam p) +
      99 * ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p))]
  have h1' : ∫ W, (100 / 99 * (Qf M P lam W p - qsl M P lam p) ^ 2 +
        100 * ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2)
        ∂stdGauss (J × Fin n) =
      100 / 99 * ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) +
      100 * ∫ W, ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2
        ∂stdGauss (J × Fin n) := by
    rw [integral_add (iQ.const_mul _) (iE.const_mul _), integral_const_mul, integral_const_mul]
  have h2 : ∫ W, ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2
        ∂stdGauss (J × Fin n) ≤
      ∫ W, (msl M P lam W p - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) := by
    have := var_le_sq (stdGauss (J × Fin n)) (fun W => (msl M P lam W p - mbar M P lam p) ^ 2)
      ((te.pow 2).int_left p) (((te.pow 2).pow 2).int_left p)
    refine this.trans (le_of_eq ?_)
    congr 1; funext W; ring
  have h3 : ∫ W, (msl M P lam W p - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) ≤
      K4 * vsl M P lam p ^ 2 := by
    obtain ⟨Q0, hdeg, hev⟩ := hpolyW
    have := h4 (J × Fin n) (Q0 - MvPolynomial.C (mbar M P lam p))
      ((MvPolynomial.totalDegree_sub_C_le Q0 _).trans hdeg)
    simp only [map_sub, MvPolynomial.eval_C, hev] at this
    exact this
  have hv0 := v_nonneg M P lam p
  have hq0 := q_nonneg M P lam hT p
  have hvq : vsl M P lam p ≤ Lam * qsl M P lam p :=
    (hD P lam p).trans (mul_le_mul_of_nonneg_left (L_le_q M P lam hT p) hL)
  have h6 : 10000 * (K4 * vsl M P lam p ^ 2) ≤ Lam * CRH * qsl M P lam p ^ 2 := by
    have a1 : vsl M P lam p ^ 2 ≤ (Lam * qsl M P lam p) ^ 2 := pow_le_pow_left₀ hv0 hvq 2
    have a2 : K4 * vsl M P lam p ^ 2 ≤ K4 * (Lam * qsl M P lam p) ^ 2 :=
      mul_le_mul_of_nonneg_left a1 hK0
    have a3 : 10000 * (K4 * (Lam * qsl M P lam p) ^ 2) =
        (10000 * (K4 * Lam)) * (Lam * qsl M P lam p ^ 2) := by ring
    have a4 : (10000 * (K4 * Lam)) * (Lam * qsl M P lam p ^ 2) ≤
        CRH * (Lam * qsl M P lam p ^ 2) :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg hL (sq_nonneg _))
    have a5 : CRH * (Lam * qsl M P lam p ^ 2) = Lam * CRH * qsl M P lam p ^ 2 := by ring
    linarith
  have hX0 : 0 ≤ Lam * CRH * qsl M P lam p ^ 2 :=
    mul_nonneg (mul_nonneg hL hC0) (sq_nonneg _)
  have e1 : 100 / 99 * (Lam * CRH) * qsl M P lam p ^ 2 =
      100 / 99 * (Lam * CRH * qsl M P lam p ^ 2) := by ring
  have e2 : 104 / 100 * (Lam * CRH) * qsl M P lam p ^ 2 =
      104 / 100 * (Lam * CRH * qsl M P lam p ^ 2) := by ring
  rw [e1] at hVQ
  rw [e2]
  linarith

end slices

/-- The conjuncts of the Gaussian model that do not use the reverse Hölder inequality, from a
bound on the variance of `Vdn` about `Vb = E_p (q_p − v_p)`. -/
lemma gmp_core (M : Mod n I J S G) (d k : ℕ) (Lam cV : ℝ) (hn : 2 ≤ n)
    (hR : Reg M d) (hPF : PolyFacts M d) (hD : Decor86 M Lam) (hSc : Scale86 M k)
    (hL : 0 ≤ Lam)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (hP : P.totalDegree ≤ k) (lam : ℝ)
    (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ))
    (hV : ∫ W, (Vdn M P lam W - ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi) ^ 2
        ∂stdGauss (J × Fin n) ≤ cV / (n : ℝ) * (∫ p, qsl M P lam p ∂M.pi) ^ 2) :
    GMP M P lam (n * Lam + 2) cV Lam := by
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have tq := t_q M P lam hT
  have tv := t_v M P lam hT
  have tL := t_L M P lam hT
  have tY := t_Y M P lam hT
  have tm := t_msl M P lam hT
  have tg := t_gsl M P hT
  have iq : Integrable (fun p => qsl M P lam p) M.pi := tq.int_par M.pi
  have iv : Integrable (fun p => vsl M P lam p) M.pi := tv.int_par M.pi
  have iL : Integrable (fun p => Lsl M P lam p) M.pi := tL.int_par M.pi
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hLv0 : 0 ≤ ∫ p, qsl M P lam p ∂M.pi := integral_nonneg (q_nonneg M P lam hT)
  have hvq : ∀ p, vsl M P lam p ≤ Lam * qsl M P lam p := fun p =>
    (hD P lam p).trans (mul_le_mul_of_nonneg_left (L_le_q M P lam hT p) hL)
  have tE : Tame (fun (W : J × Fin n → ℝ) (p : S) => (msl M P lam W p - gsl M P p) ^ 2) :=
    (tm.sub tg).pow 2
  have tVd : Tame (fun (W : J × Fin n → ℝ) (_ : Unit) => Vdn M P lam W) := tY.intAll M.pi
  refine ⟨∫ p, qsl M P lam p ∂M.pi, ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi, hLv0,
    ?_, ?_, ?_, ?_, hV, ?_⟩
  · rw [← integral_const_mul]
    exact integral_mono (iq.const_mul _) (iq.sub iv) (fun p => by
      have := hvq p
      show (1 - Lam) * qsl M P lam p ≤ qsl M P lam p - vsl M P lam p
      linarith)
  · exact (tE.intAll M.pi).int_left ()
  · exact ((tVd.sub (Tame.const _)).pow 2).int_left ()
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

/-- **The Gaussian model given the anchors, with the constant `104/100`.** -/
theorem gaussModel89 (M : Mod n I J S G) (d k : ℕ) (Lam CRH K4 : ℝ) (hn : 2 ≤ n)
    (hR : Reg M d) (hPF : PolyFacts M d) (hD : Decor86 M Lam) (hSc : Scale86 M k)
    (hRH : SliceRH M (d * k) CRH) (h4 : Fourth84 k K4)
    (hL : 0 ≤ Lam) (hLC : Lam * CRH ≤ 1 / 100) (hK : 10000 * (K4 * Lam) ≤ CRH) (hK0 : 0 ≤ K4)
    (hC0 : 0 ≤ CRH) :
    GaussModel86 M k (n * Lam + 2) (104 / 100 * n * Lam * CRH) Lam := by
  intro P hP lam hlam
  refine gmp_core M d k Lam _ hn hR hPF hD hSc hL P hP lam hlam ?_
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
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  set Vb := ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi with hVb
  set Lv := ∫ p, qsl M P lam p ∂M.pi with hLv
  have th : Tame (fun (W : J × Fin n → ℝ) (p : S) =>
      Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) := tY.sub (tq.sub tv)
  have tH : Tame (fun (W : J × Fin n → ℝ) (z : S × S) =>
      (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
      (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2))) :=
    (th.comp_right measurable_fst).mul (th.comp_right measurable_snd)
  have e1 : ∀ W, (Vdn M P lam W - Vb) ^ 2 =
      ∫ z, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
        (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂(M.pi.prod M.pi) := by
    intro W
    have a : Vdn M P lam W - Vb =
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
    have hA0 : 0 ≤ ∫ W, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) ^ 2
        ∂stdGauss (J × Fin n) := integral_nonneg fun W => sq_nonneg _
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
  have e : 104 / 100 * (n : ℝ) * Lam * CRH / n * Lv ^ 2 =
      104 / 100 * (Lam * CRH) * (Lv * Lv) := by
    field_simp
  rw [e]; exact h1

/-- **The Gaussian model for one polynomial from an abstract variance bound.** -/
theorem gaussModelV (M : Mod n I J S G) (d k : ℕ) (Lam cV : ℝ) (hn : 2 ≤ n)
    (hR : Reg M d) (hPF : PolyFacts M d) (hD : Decor86 M Lam) (hSc : Scale86 M k)
    (hL : 0 ≤ Lam) (hcV : 0 ≤ cV)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (hP : P.totalDegree ≤ k) (lam : ℝ)
    (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ))
    (hV : ∫ W, (Vdn M P lam W - ∫ p, Ybar M P lam p ∂M.pi) ^ 2 ∂stdGauss (J × Fin n) ≤
        cV / (n : ℝ) * (∫ p, Ybar M P lam p ∂M.pi) ^ 2) :
    GMP M P lam (n * Lam + 2) cV Lam := by
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have hY : (fun p => Ybar M P lam p) = fun p => qsl M P lam p - vsl M P lam p :=
    funext fun p => Ybar_eq M P lam hT p
  rw [hY] at hV
  refine gmp_core M d k Lam cV hn hR hPF hD hSc hL P hP lam hlam (hV.trans ?_)
  have iq : Integrable (fun p => qsl M P lam p) M.pi := (t_q M P lam hT).int_par M.pi
  have iv : Integrable (fun p => vsl M P lam p) M.pi := (t_v M P lam hT).int_par M.pi
  have h0 : 0 ≤ ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi :=
    integral_nonneg fun p => by
      have := Ybar_nonneg M P lam p
      rw [Ybar_eq M P lam hT p] at this
      exact this
  have h1 : ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi ≤ ∫ p, qsl M P lam p ∂M.pi :=
    integral_mono (iq.sub iv) iq fun p => by
      have := v_nonneg M P lam p
      show qsl M P lam p - vsl M P lam p ≤ qsl M P lam p
      linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) (div_nonneg hcV (Nat.cast_nonneg n))

end BstLean.Part89

#print axioms BstLean.Part89.gaussModel89
#print axioms BstLean.Part89.gaussModelV
#print axioms BstLean.Part89.Ybar_eq
#print axioms BstLean.Part89.Ybar_nonneg
