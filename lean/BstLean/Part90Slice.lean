import BstLean.Part90Defs

/-!
# Part 90: the variance bound in one slice, final form (`CubSliceA`)

`cubSliceA : RegC → VarBoundC → GradL4 → CubSliceA`. The proof is real arithmetic on top of the
three interfaces: the floor of `Ȳ`, the triangle inequality in `L²(ν)` for the anchors, the
Cauchy–Schwarz inequality against the floor, and the self-referential inequality for `Var_W Y`.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU)
open BstLean.Part56 (UnitV kJ tauR polarPoint perpDir axialR axialS)
open BstLean.Part78 (nsq frobH zv)
open BstLean.Part80 (kA FeatOpA)
open BstLean.Part82 (T3 SymT frobT trT cfun aU3 HU3)
open BstLean.Part86
open BstLean.Part89 (Ybar)

/-! ## Real arithmetic -/

private lemma sq_add_le_w {p q ω : ℝ} (hω : 0 < ω) :
    (p + q) ^ 2 ≤ (1 + ω) * p ^ 2 + (1 + 1 / ω) * q ^ 2 := by
  have e : (1 + ω) * p ^ 2 + (1 + 1 / ω) * q ^ 2 - (p + q) ^ 2 = (ω * p - q) ^ 2 / ω := by
    field_simp; ring
  have : 0 ≤ (ω * p - q) ^ 2 / ω := by positivity
  linarith

private lemma sq_le_split {β u c : ℝ} (hc : 0 < c) :
    β ^ 2 ≤ (1 + c) * u ^ 2 + (1 + 1 / c) * (u - β) ^ 2 := by
  have e : (1 + c) * u ^ 2 + (1 + 1 / c) * (u - β) ^ 2 - β ^ 2 = (c * u + (u - β)) ^ 2 / c := by
    field_simp; ring
  have : 0 ≤ (c * u + (u - β)) ^ 2 / c := by positivity
  linarith

private lemma cs3 {x1 x2 x3 y p q : ℝ} (h : x1 ^ 2 + 2 * x2 ^ 2 + 6 * x3 ^ 2 ≤ y) :
    (x1 + p * x2 + q * x3) ^ 2 ≤ (1 + p ^ 2 / 2 + q ^ 2 / 6) * y := by
  have hC : 0 ≤ 1 + p ^ 2 / 2 + q ^ 2 / 6 := by positivity
  have h1 := mul_le_mul_of_nonneg_left h hC
  have e : (1 + p ^ 2 / 2 + q ^ 2 / 6) * (x1 ^ 2 + 2 * x2 ^ 2 + 6 * x3 ^ 2) -
      (x1 + p * x2 + q * x3) ^ 2 =
      (x1 * p - 2 * x2) ^ 2 / 2 + (x1 * q - 6 * x3) ^ 2 / 6 + (x2 * q - 3 * x3 * p) ^ 2 / 3 := by
    ring
  have : 0 ≤ (x1 * p - 2 * x2) ^ 2 / 2 + (x1 * q - 6 * x3) ^ 2 / 6 +
      (x2 * q - 3 * x3 * p) ^ 2 / 3 := by positivity
  linarith

private lemma cs2 {x1 x2 x3 y p q : ℝ} (h : x1 ^ 2 + 2 * x2 ^ 2 + 6 * x3 ^ 2 ≤ y) :
    (p * x2 + q * x3) ^ 2 ≤ (p ^ 2 / 2 + q ^ 2 / 6) * y := by
  have hC : 0 ≤ p ^ 2 / 2 + q ^ 2 / 6 := by positivity
  have h1 := mul_le_mul_of_nonneg_left h hC
  have e : (p ^ 2 / 2 + q ^ 2 / 6) * (x1 ^ 2 + 2 * x2 ^ 2 + 6 * x3 ^ 2) -
      (p * x2 + q * x3) ^ 2 =
      (p ^ 2 / 2 + q ^ 2 / 6) * x1 ^ 2 + (3 * p * x3 - q * x2) ^ 2 / 3 := by
    ring
  have : 0 ≤ (p ^ 2 / 2 + q ^ 2 / 6) * x1 ^ 2 + (3 * p * x3 - q * x2) ^ 2 / 3 := by positivity
  linarith

/-- The self-referential inequality. -/
private lemma step4 {v Y a b s ζ : ℝ} (hv : 0 ≤ v) (hY : 0 ≤ Y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ Y ^ 2 + v) (hvb : v ≤ a * Y + b * s) (hζ : 0 < ζ) :
    v ≤ (b + ζ * Y / 2 + (a + b) / (2 * ζ)) ^ 2 := by
  have hσ0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hσ2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  generalize Real.sqrt v = σ at hσ0 hσ2
  have hsle : s ≤ Y + σ := by
    have : s ^ 2 ≤ (Y + σ) ^ 2 := by nlinarith [mul_nonneg hY hσ0]
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  have h1 : σ ^ 2 ≤ (a + b) * Y + b * σ := by
    nlinarith [mul_le_mul_of_nonneg_left hsle hb]
  have hR : 0 ≤ ζ * Y / 2 + (a + b) / (2 * ζ) := by positivity
  have key : σ ≤ b + ζ * Y / 2 + (a + b) / (2 * ζ) := by
    by_cases hc : σ ≤ b
    · linarith
    · push Not at hc
      have h2 : (σ - b) ^ 2 ≤ (a + b) * Y := by nlinarith
      have h3 : (a + b) * Y ≤ (ζ * Y / 2 + (a + b) / (2 * ζ)) ^ 2 := by
        have e : (ζ * Y / 2 + (a + b) / (2 * ζ)) ^ 2 - (a + b) * Y =
            (ζ * Y / 2 - (a + b) / (2 * ζ)) ^ 2 := by
          field_simp; ring
        nlinarith [sq_nonneg (ζ * Y / 2 - (a + b) / (2 * ζ))]
      have := (abs_le_of_sq_le_sq' (h2.trans h3) hR).2
      linarith
  rw [← hσ2]
  exact pow_le_pow_left₀ hσ0 key 2

/-- `N ≤ (1+c) A + (1+1/c) B` for every `c > 0` gives `√N ≤ √A + d` when `B ≤ d²`. -/
private lemma real_tri {N A B d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) (hBd : B ≤ d ^ 2)
    (h : ∀ c : ℝ, 0 < c → N ≤ (1 + c) * A + (1 + 1 / c) * B) :
    Real.sqrt N ≤ Real.sqrt A + d := by
  have ha0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have ha2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  generalize Real.sqrt A = a at ha0 ha2
  subst ha2
  have claim : N ≤ (a + d) ^ 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hden : 0 < 4 * (a + d) + 4 := by positivity
    set δ := min 1 (ε / (4 * (a + d) + 4)) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (div_pos hε hden)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ * (4 * (a + d) + 4) ≤ ε := by
      have : δ ≤ ε / (4 * (a + d) + 4) := min_le_right _ _
      rwa [le_div_iff₀ hden] at this
    have hu : 0 < a + δ := by linarith
    have hw : 0 < d + δ := by linarith
    have hc : 0 < (d + δ) / (a + δ) := div_pos hw hu
    have h1 := h _ hc
    rw [one_div_div] at h1
    have h2 : (1 + (d + δ) / (a + δ)) * a ^ 2 + (1 + (a + δ) / (d + δ)) * B ≤
        (1 + (d + δ) / (a + δ)) * (a + δ) ^ 2 + (1 + (a + δ) / (d + δ)) * (d + δ) ^ 2 := by
      have hk1 : 0 ≤ 1 + (d + δ) / (a + δ) := by positivity
      have hk2 : 0 ≤ 1 + (a + δ) / (d + δ) := by positivity
      have i1 : a ^ 2 ≤ (a + δ) ^ 2 := by nlinarith
      have i2 : B ≤ (d + δ) ^ 2 := by nlinarith
      exact add_le_add (mul_le_mul_of_nonneg_left i1 hk1) (mul_le_mul_of_nonneg_left i2 hk2)
    have e : (1 + (d + δ) / (a + δ)) * (a + δ) ^ 2 + (1 + (a + δ) / (d + δ)) * (d + δ) ^ 2 =
        (a + d + 2 * δ) ^ 2 := by
      field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ0.le]
  calc Real.sqrt N ≤ Real.sqrt ((a + d) ^ 2) := Real.sqrt_le_sqrt claim
    _ = a + d := Real.sqrt_sq (by positivity)

/-- Steps 3–5 of the paper proof. -/
private lemma arith_main {Lam g4 t rt cH cT e1 e2 e4 z sA sH tt hb nA Y v s η ω ζ : ℝ}
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (hg : 0 ≤ g4) (hrt : 0 ≤ rt) (ht : rt ^ 2 = t)
    (hcH : 0 ≤ cH) (hcT : 0 ≤ cT) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (hz : 0 ≤ z)
    (hsA : 0 ≤ sA) (hsH : 0 ≤ sH) (htt : 0 ≤ tt) (hhb : 0 ≤ hb) (hnA : 0 ≤ nA)
    (hY : 0 ≤ Y) (hv : 0 ≤ v) (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ Y ^ 2 + v)
    (hfloor : (1 - Lam) * (t * sA ^ 2 + 2 * t ^ 2 * sH ^ 2 + 6 * t ^ 3 * tt ^ 2) ≤ Y)
    (hA : nA ≤ sA + (e1 * rt * hb + e2 * t * tt + z))
    (hH : hb ≤ sH + e4 * rt * tt)
    (hη : 0 < η) (hω : 0 < ω) (hζ : 0 < ζ)
    (hvb : v ≤ 4 * (1 + η) * nA ^ 2 * (Lam * t) * Y + 4 * (1 + 1 / η) * (g4 * (Lam * t)) * s *
      (e1 * rt * hb + e2 * t * tt + z + cH * rt * (hb + e4 * rt * tt) + cT * t * tt) ^ 2) :
    v ≤ (kYc Lam g4 η ω ζ cH cT e1 e2 e4 * Y + kEc Lam g4 η ω ζ * (t * z ^ 2)) ^ 2 := by
  subst ht
  have hL : 0 < 1 - Lam := by linarith
  have hy0 : 0 ≤ Y / (1 - Lam) := div_nonneg hY hL.le
  generalize hDdef : e1 * rt * hb + e2 * rt ^ 2 * tt + z + cH * rt * (hb + e4 * rt * tt) +
    cT * rt ^ 2 * tt = D at hvb
  have hD0 : 0 ≤ D := by rw [← hDdef]; positivity
  have hQ : (rt * sA) ^ 2 + 2 * (rt ^ 2 * sH) ^ 2 + 6 * (rt ^ 2 * rt * tt) ^ 2 ≤ Y / (1 - Lam) := by
    rw [le_div_iff₀ hL]
    have e : (rt * sA) ^ 2 + 2 * (rt ^ 2 * sH) ^ 2 + 6 * (rt ^ 2 * rt * tt) ^ 2 =
        rt ^ 2 * sA ^ 2 + 2 * (rt ^ 2) ^ 2 * sH ^ 2 + 6 * (rt ^ 2) ^ 3 * tt ^ 2 := by ring
    rw [e]; linarith
  generalize hy : Y / (1 - Lam) = y at hQ hy0
  generalize hx1 : rt * sA = x1 at hQ
  generalize hx2 : rt ^ 2 * sH = x2 at hQ
  generalize hx3 : rt ^ 2 * rt * tt = x3 at hQ
  have hx10 : 0 ≤ x1 := by rw [← hx1]; positivity
  have hx20 : 0 ≤ x2 := by rw [← hx2]; positivity
  have hx30 : 0 ≤ x3 := by rw [← hx3]; positivity
  have hthb : rt ^ 2 * hb ≤ x2 + e4 * x3 := by
    have := mul_le_mul_of_nonneg_left hH (sq_nonneg rt)
    rw [← hx2, ← hx3]; linarith
  have hrtdA : rt * (e1 * rt * hb + e2 * rt ^ 2 * tt + z) ≤
      e1 * (x2 + e4 * x3) + e2 * x3 + rt * z := by
    have := mul_le_mul_of_nonneg_left hthb he1
    rw [← hx3] at this ⊢; linarith
  have hP : rt * nA ≤ (x1 + e1 * x2 + (e1 * e4 + e2) * x3) + rt * z := by
    have := mul_le_mul_of_nonneg_left hA hrt
    rw [← hx1]; linarith
  have hRD : rt * D ≤ ((cH + e1) * x2 + (cT + 2 * cH * e4 + e1 * e4 + e2) * x3) + rt * z := by
    have h1 := mul_le_mul_of_nonneg_left hthb hcH
    rw [← hDdef]
    rw [← hx3] at hrtdA h1 ⊢; linarith
  have hE : (rt * z) ^ 2 = rt ^ 2 * z ^ 2 := by ring
  have hTA : rt ^ 2 * nA ^ 2 ≤ (1 + ω) * (C1c e1 e2 e4 * y) + (1 + 1 / ω) * (rt ^ 2 * z ^ 2) := by
    have h1 : (rt * nA) ^ 2 ≤ ((x1 + e1 * x2 + (e1 * e4 + e2) * x3) + rt * z) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hP 2
    have h2 := sq_add_le_w (p := x1 + e1 * x2 + (e1 * e4 + e2) * x3) (q := rt * z) hω
    have h3 : (x1 + e1 * x2 + (e1 * e4 + e2) * x3) ^ 2 ≤ C1c e1 e2 e4 * y := cs3 hQ
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + ω)
    rw [hE] at h2
    have e : rt ^ 2 * nA ^ 2 = (rt * nA) ^ 2 := by ring
    rw [e]; linarith
  have hTD : rt ^ 2 * D ^ 2 ≤
      (1 + ω) * (C3c cH cT e1 e2 e4 * y) + (1 + 1 / ω) * (rt ^ 2 * z ^ 2) := by
    have h1 : (rt * D) ^ 2 ≤
        (((cH + e1) * x2 + (cT + 2 * cH * e4 + e1 * e4 + e2) * x3) + rt * z) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRD 2
    have h2 := sq_add_le_w (p := (cH + e1) * x2 + (cT + 2 * cH * e4 + e1 * e4 + e2) * x3)
      (q := rt * z) hω
    have h3 : ((cH + e1) * x2 + (cT + 2 * cH * e4 + e1 * e4 + e2) * x3) ^ 2 ≤
        C3c cH cT e1 e2 e4 * y := cs2 hQ
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + ω)
    rw [hE] at h2
    have e : rt ^ 2 * D ^ 2 = (rt * D) ^ 2 := by ring
    rw [e]; linarith
  generalize hEdef : rt ^ 2 * z ^ 2 = E at hTA hTD ⊢
  have hE0 : 0 ≤ E := by rw [← hEdef]; positivity
  have hC1 : 0 ≤ C1c e1 e2 e4 := by unfold C1c; positivity
  have hC3 : 0 ≤ C3c cH cT e1 e2 e4 := by unfold C3c; positivity
  have hηi : 0 ≤ 1 / η := by positivity
  have hωi : 0 ≤ 1 / ω := by positivity
  have hc1 : 0 ≤ c1c η ω e1 e2 e4 := by unfold c1c; positivity
  have hc2 : 0 ≤ c2c η ω := by unfold c2c; positivity
  have hc3 : 0 ≤ c3c g4 η ω cH cT e1 e2 e4 := by unfold c3c; positivity
  have hc4 : 0 ≤ c4c g4 η ω := by unfold c4c; positivity
  have ha_le : 4 * (1 + η) * Lam * (rt ^ 2 * nA ^ 2) ≤
      Lam * (c1c η ω e1 e2 e4 * y + c2c η ω * E) := by
    have := mul_le_mul_of_nonneg_left hTA (by positivity : (0 : ℝ) ≤ 4 * (1 + η) * Lam)
    unfold c1c c2c; linarith
  have hb_le : 4 * (1 + 1 / η) * g4 * Lam * (rt ^ 2 * D ^ 2) ≤
      Lam * (c3c g4 η ω cH cT e1 e2 e4 * y + c4c g4 η ω * E) := by
    have := mul_le_mul_of_nonneg_left hTD (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * g4 * Lam)
    unfold c3c c4c; linarith
  have hvb' : v ≤ 4 * (1 + η) * Lam * (rt ^ 2 * nA ^ 2) * Y +
      4 * (1 + 1 / η) * g4 * Lam * (rt ^ 2 * D ^ 2) * s := by
    calc v ≤ _ := hvb
      _ = _ := by ring
  generalize 4 * (1 + η) * Lam * (rt ^ 2 * nA ^ 2) = a at ha_le hvb'
  generalize 4 * (1 + 1 / η) * g4 * Lam * (rt ^ 2 * D ^ 2) = b at hb_le hvb'
  unfold kYc kEc
  generalize c1c η ω e1 e2 e4 = c1 at *
  generalize c2c η ω = c2 at *
  generalize c3c g4 η ω cH cT e1 e2 e4 = c3 at *
  generalize c4c g4 η ω = c4 at *
  -- `a`, `b` may be replaced by `max a 0`, `max b 0`
  have ha0 : 0 ≤ max a 0 := le_max_right _ _
  have hb0 : 0 ≤ max b 0 := le_max_right _ _
  have hA' : 0 ≤ Lam * (c1 * y + c2 * E) := by positivity
  have hB' : 0 ≤ Lam * (c3 * y + c4 * E) := by positivity
  have ha_le' : max a 0 ≤ Lam * (c1 * y + c2 * E) := max_le ha_le hA'
  have hb_le' : max b 0 ≤ Lam * (c3 * y + c4 * E) := max_le hb_le hB'
  have hvb'' : v ≤ max a 0 * Y + max b 0 * s := by
    have h1 := mul_le_mul_of_nonneg_right (le_max_left a 0) hY
    have h2 := mul_le_mul_of_nonneg_right (le_max_left b 0) hs
    linarith
  have h5 := step4 hv hY ha0 hb0 hs hs2 hvb'' hζ
  have h6 : max b 0 + ζ * Y / 2 + (max a 0 + max b 0) / (2 * ζ) ≤
      (Lam * c3 / (1 - Lam) + ζ / 2 + Lam * (c1 + c3) / ((1 - Lam) * (2 * ζ))) * Y +
        Lam * (c4 + (c2 + c4) / (2 * ζ)) * E := by
    have h7 : (max a 0 + max b 0) / (2 * ζ) ≤
        (Lam * (c1 * y + c2 * E) + Lam * (c3 * y + c4 * E)) / (2 * ζ) :=
      div_le_div_of_nonneg_right (add_le_add ha_le' hb_le') (by positivity)
    have e : Lam * (c3 * y + c4 * E) + ζ * Y / 2 +
        (Lam * (c1 * y + c2 * E) + Lam * (c3 * y + c4 * E)) / (2 * ζ) =
        (Lam * c3 / (1 - Lam) + ζ / 2 + Lam * (c1 + c3) / ((1 - Lam) * (2 * ζ))) * Y +
          Lam * (c4 + (c2 + c4) / (2 * ζ)) * E := by
      rw [← hy]; field_simp; ring
    linarith
  calc v ≤ _ := h5
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h6 2

/-! ## Integrals -/

private lemma nsq_nn {n : ℕ} (a : Fin n → ℝ) : 0 ≤ nsq a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma frobH_nn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobH M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma frobT_nn {n : ℕ} (T : T3 n) : 0 ≤ frobT T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _

private lemma nsq_split {n : ℕ} (A Abar : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    nsq Abar ≤ (1 + c) * nsq A + (1 + 1 / c) * nsq (fun i => A i - Abar i) := by
  unfold nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => sq_le_split hc

private lemma frobH_split {n : ℕ} (A Abar : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : 0 < c) :
    frobH Abar ≤ (1 + c) * frobH A + (1 + 1 / c) * frobH (A - Abar) := by
  unfold frobH
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.sub_apply]
  exact sq_le_split hc

private lemma var_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → ℝ} (hq : Integrable q μ) (hq2 : Integrable (fun x => q x ^ 2) μ) :
    ∫ x, (q x - ∫ y, q y ∂μ) ^ 2 ∂μ = ∫ x, q x ^ 2 ∂μ - (∫ y, q y ∂μ) ^ 2 := by
  generalize hB : ∫ y, q y ∂μ = B
  have e : (fun x => (q x - B) ^ 2) = fun x => q x ^ 2 - 2 * B * q x + B ^ 2 := by
    funext x; ring
  rw [e, integral_add (show Integrable (fun x => q x ^ 2 - 2 * B * q x) μ from
      hq2.sub (hq.const_mul _)) (integrable_const _),
    integral_sub hq2 (hq.const_mul _), integral_const_mul, integral_const, hB]
  simp
  ring

private lemma tri_int {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {p q : X → ℝ} {N d : ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hq2 : Integrable (fun x => q x ^ 2) μ) (hp0 : ∀ x, 0 ≤ p x) (hd : 0 ≤ d)
    (hpt : ∀ c : ℝ, 0 < c → ∀ x, N ≤ (1 + c) * p x + (1 + 1 / c) * q x)
    (hqd : ∫ x, q x ^ 2 ∂μ ≤ d ^ 4) :
    Real.sqrt N ≤ Real.sqrt (∫ x, p x ∂μ) + d := by
  have hA0 : 0 ≤ ∫ x, p x ∂μ := integral_nonneg hp0
  have hBsq : (∫ x, q x ∂μ) ^ 2 ≤ ∫ x, q x ^ 2 ∂μ := by
    have h0 : 0 ≤ ∫ x, (q x - ∫ y, q y ∂μ) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    rw [var_eq hq hq2] at h0
    linarith
  have hBd : ∫ x, q x ∂μ ≤ d ^ 2 := by
    by_contra hc
    push Not at hc
    nlinarith [sq_nonneg d]
  refine real_tri hA0 hd hBd fun c hc => ?_
  have := integral_mono (integrable_const N)
    (show Integrable (fun x => (1 + c) * p x + (1 + 1 / c) * q x) μ from
      (hp.const_mul (1 + c)).add (hq.const_mul (1 + 1 / c))) (hpt c hc)
  rw [integral_const, integral_add (hp.const_mul _) (hq.const_mul _), integral_const_mul,
    integral_const_mul] at this
  simpa using this

theorem cubSliceA (hR : RegC) (hV : VarBoundC) (hG : GradL4) : CubSliceA := by
  intro n J _ ν hν f0 ℓ H hH T hT mu ψ hmu hψ Lam g4 K t rt cH cT hL0 hL1 hg hK hrt ht hcH hcT
    hcH4 hcT4 hFO hF4 hk hfl Abar Hbar e1 e2 e4 z he1 he2 he4 hz hoA hoH η ω ζ hη hω hζ
  have := hν.prob
  have ht0 : 0 ≤ t := ht ▸ sq_nonneg rt
  have hmui : ∀ i, Continuous fun x => mu x i := fun i => (continuous_apply i).comp hmu
  have hψq : ∀ q, Continuous fun x => ψ x q := fun q => (continuous_apply q).comp hψ
  have hkc : Continuous fun x => kA ψ x := by
    unfold kA
    exact continuous_finsetSum _ fun q _ => (hψq q).pow 2
  have hAi : ∀ i, Continuous fun x => AxC ℓ H T mu ψ x i := by
    intro i
    unfold AxC aU3
    refine ((continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun j _ => continuous_const.mul (hmui j)))).add
      (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        continuous_finsetSum _ fun k _ => (continuous_const.mul (hmui j)).mul (hmui k)))).add
      ((continuous_const.mul hkc).mul continuous_const)
  have hHij : ∀ i j, Continuous fun x => HxC H T mu x i j := by
    intro i j
    simp only [HxC, HU3, Matrix.of_apply]
    exact continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hmui k)))
  have cpA : Continuous fun x => nsq (AxC ℓ H T mu ψ x) := by
    unfold nsq
    exact continuous_finsetSum _ fun i _ => (hAi i).pow 2
  have cqA : Continuous fun x => nsq (fun i => AxC ℓ H T mu ψ x i - Abar i) := by
    unfold nsq
    exact continuous_finsetSum _ fun i _ => ((hAi i).sub continuous_const).pow 2
  have cpH : Continuous fun x => frobH (HxC H T mu x) := by
    unfold frobH
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hHij i j).pow 2
  have cqH : Continuous fun x => frobH (HxC H T mu x - Hbar) := by
    unfold frobH
    simp only [Matrix.sub_apply]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hHij i j).sub continuous_const).pow 2
  have cw : Continuous fun x => wC ℓ H T mu ψ x := by
    unfold wC
    exact (((hkc.mul cpA).add ((continuous_const.mul (hkc.pow 2)).mul cpH)).add
      ((continuous_const.mul (hkc.pow 3)).mul continuous_const))
  have I := fun {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) =>
    BstLean.Part56.integrable_cont_sph56 hν hf
  -- notation
  have hT0 := frobT_nn T
  have hHb0 := frobH_nn Hbar
  have htt2 : Real.sqrt (frobT T) ^ 2 = frobT T := Real.sq_sqrt hT0
  have hhb2 : Real.sqrt (frobH Hbar) ^ 2 = frobH Hbar := Real.sq_sqrt hHb0
  have htt0 := Real.sqrt_nonneg (frobT T)
  have hhb0 := Real.sqrt_nonneg (frobH Hbar)
  have hdA0 : 0 ≤ e1 * rt * Real.sqrt (frobH Hbar) + e2 * t * Real.sqrt (frobT T) + z := by
    positivity
  have hdH0 : 0 ≤ e4 * rt * Real.sqrt (frobT T) := by positivity
  have hA2 : 0 ≤ ∫ x, nsq (AxC ℓ H T mu ψ x) ∂ν := integral_nonneg fun _ => nsq_nn _
  have hH2 : 0 ≤ ∫ x, frobH (HxC H T mu x) ∂ν := integral_nonneg fun _ => frobH_nn _
  -- Step 0 (b), (c)
  have hb : Real.sqrt (nsq Abar) ≤ Real.sqrt (∫ x, nsq (AxC ℓ H T mu ψ x) ∂ν) +
      (e1 * rt * Real.sqrt (frobH Hbar) + e2 * t * Real.sqrt (frobT T) + z) :=
    tri_int (I cpA) (I cqA) (I (cqA.pow 2)) (fun _ => nsq_nn _) hdA0
      (fun c hc x => nsq_split _ _ hc) hoA
  have hc : Real.sqrt (frobH Hbar) ≤ Real.sqrt (∫ x, frobH (HxC H T mu x) ∂ν) +
      e4 * rt * Real.sqrt (frobT T) :=
    tri_int (I cpH) (I cqH) (I (cqH.pow 2)) (fun _ => frobH_nn _) hdH0
      (fun c hc x => frobH_split _ _ hc) hoH
  -- Step 0 (a)
  have hw : t * ∫ x, nsq (AxC ℓ H T mu ψ x) ∂ν + 2 * t ^ 2 * ∫ x, frobH (HxC H T mu x) ∂ν +
      6 * t ^ 3 * frobT T ≤ ∫ x, wC ℓ H T mu ψ x ∂ν := by
    have i1 : Integrable (fun x => t * nsq (AxC ℓ H T mu ψ x)) ν := (I cpA).const_mul _
    have i2 : Integrable (fun x => 2 * t ^ 2 * frobH (HxC H T mu x)) ν := (I cpH).const_mul _
    have i12 : Integrable (fun x => t * nsq (AxC ℓ H T mu ψ x) +
        2 * t ^ 2 * frobH (HxC H T mu x)) ν := i1.add i2
    have i123 : Integrable (fun x => t * nsq (AxC ℓ H T mu ψ x) +
        2 * t ^ 2 * frobH (HxC H T mu x) + 6 * t ^ 3 * frobT T) ν := i12.add (integrable_const _)
    have e : ∫ x, (t * nsq (AxC ℓ H T mu ψ x) + 2 * t ^ 2 * frobH (HxC H T mu x) +
        6 * t ^ 3 * frobT T) ∂ν = t * ∫ x, nsq (AxC ℓ H T mu ψ x) ∂ν +
        2 * t ^ 2 * ∫ x, frobH (HxC H T mu x) ∂ν + 6 * t ^ 3 * frobT T := by
      rw [integral_add i12 (integrable_const _), integral_add i1 i2,
        integral_const_mul, integral_const_mul, integral_const]
      simp
    rw [← e]
    refine integral_mono_ae i123 (I cw) ?_
    filter_upwards [hk] with x hx
    have hk0 : 0 ≤ kA ψ x := ht0.trans hx.1
    have h2 : t ^ 2 ≤ kA ψ x ^ 2 := pow_le_pow_left₀ ht0 hx.1 2
    have h3 : t ^ 3 ≤ kA ψ x ^ 3 := pow_le_pow_left₀ ht0 hx.1 3
    have j1 := mul_le_mul_of_nonneg_right hx.1 (nsq_nn (AxC ℓ H T mu ψ x))
    have j2 := mul_le_mul_of_nonneg_right h2 (frobH_nn (HxC H T mu x))
    have j3 := mul_le_mul_of_nonneg_right h3 hT0
    show _ ≤ wC ℓ H T mu ψ x
    unfold wC
    linarith
  have hfloor : (1 - Lam) * (t * Real.sqrt (∫ x, nsq (AxC ℓ H T mu ψ x) ∂ν) ^ 2 +
      2 * t ^ 2 * Real.sqrt (∫ x, frobH (HxC H T mu x) ∂ν) ^ 2 +
      6 * t ^ 3 * Real.sqrt (frobT T) ^ 2) ≤ YbC ν f0 ℓ H T mu ψ := by
    rw [Real.sq_sqrt hA2, Real.sq_sqrt hH2, htt2]
    exact (mul_le_mul_of_nonneg_left hw (by linarith)).trans hfl
  -- Step 1
  have hD4 := hG n J ν hν ℓ H hH T hT mu ψ hmu hψ Abar Hbar K t rt cH cT
    (e1 * rt * Real.sqrt (frobH Hbar) + e2 * t * Real.sqrt (frobT T) + z)
    (e4 * rt * Real.sqrt (frobT T)) (Real.sqrt (frobH Hbar)) (Real.sqrt (frobT T))
    hK hrt ht hcH hcT hdA0 hdH0 hhb0 htt0 hcH4 hcT4 hhb2.ge htt2.ge
    (hk.mono fun x h => h.2) hoA hoH
  -- Step 2
  obtain ⟨hYi, hY2i⟩ := hR n J ν hν f0 ℓ H T mu ψ hmu hψ
  have hYb0 : 0 ≤ YbC ν f0 ℓ H T mu ψ :=
    integral_nonneg fun W => BstLean.Part41.varU_nonneg _ _
  have hv0 : 0 ≤ ∫ W, (YC ν f0 ℓ H T mu ψ W - YbC ν f0 ℓ H T mu ψ) ^ 2 ∂stdGauss (J × Fin n) :=
    integral_nonneg fun _ => sq_nonneg _
  have hve : ∫ W, (YC ν f0 ℓ H T mu ψ W - YbC ν f0 ℓ H T mu ψ) ^ 2 ∂stdGauss (J × Fin n) =
      ∫ W, YC ν f0 ℓ H T mu ψ W ^ 2 ∂stdGauss (J × Fin n) - YbC ν f0 ℓ H T mu ψ ^ 2 :=
    var_eq hYi hY2i
  have hs0 := Real.sqrt_nonneg (YbC ν f0 ℓ H T mu ψ ^ 2 +
    ∫ W, (YC ν f0 ℓ H T mu ψ W - YbC ν f0 ℓ H T mu ψ) ^ 2 ∂stdGauss (J × Fin n))
  have hs2 : Real.sqrt (YbC ν f0 ℓ H T mu ψ ^ 2 +
      ∫ W, (YC ν f0 ℓ H T mu ψ W - YbC ν f0 ℓ H T mu ψ) ^ 2 ∂stdGauss (J × Fin n)) ^ 2 =
      YbC ν f0 ℓ H T mu ψ ^ 2 +
      ∫ W, (YC ν f0 ℓ H T mu ψ W - YbC ν f0 ℓ H T mu ψ) ^ 2 ∂stdGauss (J × Fin n) :=
    Real.sq_sqrt (by positivity)
  have hvb := hV n J ν hν f0 ℓ H hH T hT mu ψ hmu hψ (Lam * t) (g4 * (Lam * t))
    (mul_nonneg hL0 ht0) (mul_nonneg hg (mul_nonneg hL0 ht0)) hFO hF4 Abar η _ _ hη
    (by positivity) hs0 hD4 (by rw [hs2]; linarith)
  rw [← Real.sq_sqrt (nsq_nn Abar)] at hvb
  exact arith_main hL0 hL1 hg hrt ht hcH hcT he1 he2 he4 hz (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) htt0 hhb0 (Real.sqrt_nonneg _) hYb0 hv0 hs0 hs2.le hfloor hb hc
    hη hω hζ hvb

end BstLean.Part90

#print axioms BstLean.Part90.cubSliceA
