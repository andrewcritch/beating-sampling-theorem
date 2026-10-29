import BstLean.Part182Def

/-!
# Part 182 (file `Schur`): the weighted Schur test, abstract form

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:dual` (the dual
operator identity, used here only through the choice `f = √w·Bᵀv`), Lemma `t7:p04:schur`
(the Schur test on good pairs, Cauchy–Schwarz on exceptional pairs) and Lemma `t7:p04:MS`
(a pair bound by one constant per pair, here a kernel `κ`). The tangential gain `χ` of the paper
is NOT used: the kernel bound is a bound for all vectors.

* `pair_of_opN`: `‖Mᵀ M'‖_op ≤ K` gives `|⟨M u, M' u'⟩| ≤ K |u||u'|` (bridge to `pairBad`).
* `nrm_vecMul_le`: `|vᵀ M| ≤ ‖M‖_op |v|`.
* `le_sqrt_of_forall_pos`, `quad_step`: two scalar steps.
* **`schur_abstract`**: `Q(v) = ∫ w |vᵀB|² ≤ (R + √(√H·∫ w²β⁴))·|v|²`, where `R` bounds the row
  integrals `∫ 1_G κ w'`, `H = μ⊗μ(Gᶜ ∩ S×S)` and `w = 0` off `S`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)

section linalg
variable {m k : ℕ}

lemma normSq_eq_dot (f : Fin k → ℝ) : normSq f = f ⬝ᵥ f := by
  simp [normSq, dotProduct, sq]

lemma nrm_mulVec_le (M : Matrix (Fin m) (Fin k) ℝ) (a : Fin k → ℝ) :
    nrm (M *ᵥ a) ≤ opN M * nrm a := mulVec_le_opN M a

lemma nrm_vecMul_le (M : Matrix (Fin m) (Fin k) ℝ) (v : Fin m → ℝ) :
    nrm (vecMul v M) ≤ opN M * nrm v := by
  set f := vecMul v M with hf
  have h1 : nrm f ^ 2 ≤ opN M * nrm v * nrm f := by
    rw [nrm_sq, normSq_eq_dot]
    have e : f ⬝ᵥ f = v ⬝ᵥ (M *ᵥ f) := by rw [dotProduct_mulVec]
    rw [e]
    refine (le_abs_self _).trans ((abs_dot_le_nrm _ _).trans ?_)
    have := nrm_mulVec_le M f
    nlinarith [nrm_nonneg v, nrm_nonneg f, opN_nonneg M]
  rcases (nrm_nonneg f).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg (opN_nonneg M) (nrm_nonneg v)
  · nlinarith

/-- **Bridge**: a bound on `‖Mᵀ M'‖_op` gives the bilinear pair bound. -/
lemma pair_of_opN (M M' : Matrix (Fin m) (Fin k) ℝ) {K : ℝ} (h : opN (Mᵀ * M') ≤ K)
    (a a' : Fin k → ℝ) : |(M *ᵥ a) ⬝ᵥ (M' *ᵥ a')| ≤ K * nrm a * nrm a' := by
  have e : (M *ᵥ a) ⬝ᵥ (M' *ᵥ a') = a ⬝ᵥ ((Mᵀ * M') *ᵥ a') := by
    rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, mulVec_transpose,
      dotProduct_comm]
  rw [e]
  refine (abs_dot_le_nrm _ _).trans ?_
  have := nrm_mulVec_le (Mᵀ * M') a'
  have h2 : opN (Mᵀ * M') * nrm a' ≤ K * nrm a' :=
    mul_le_mul_of_nonneg_right h (nrm_nonneg _)
  nlinarith [nrm_nonneg a, nrm_nonneg ((Mᵀ * M') *ᵥ a')]

lemma abs_coord_le_nrm (u : Fin k → ℝ) (i : Fin k) : |u i| ≤ nrm u := by
  unfold nrm normSq
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => u j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

end linalg

section scalar

/-- If `J ≤ (s H + C/s)/2` for every `s > 0` (with `H, C ≥ 0`), then `J ≤ √(H C)`. -/
lemma le_sqrt_of_forall_pos {J H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (h : ∀ s : ℝ, 0 < s → J ≤ (s * H + C / s) / 2) : J ≤ √(H * C) := by
  by_contra hcon
  push Not at hcon
  have hJ : 0 < J := lt_of_le_of_lt (Real.sqrt_nonneg _) hcon
  rcases hH.eq_or_lt with hH0 | hHp
  · have hs : 0 < C / J + 1 := by positivity
    have h1 := h _ hs
    rw [← hH0] at h1
    have h2 : C / (C / J + 1) < 2 * J := by
      rw [div_lt_iff₀ hs]
      have : C / J * J = C := div_mul_cancel₀ C hJ.ne'
      nlinarith
    linarith
  rcases hC.eq_or_lt with hC0 | hCp
  · have hs : 0 < J / (H + 1) := by positivity
    have h1 := h _ hs
    rw [← hC0] at h1
    have h2 : J / (H + 1) * H < 2 * J := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    simp at h1
    linarith
  · have hs : 0 < √C / √H := div_pos (Real.sqrt_pos.2 hCp) (Real.sqrt_pos.2 hHp)
    have h1 := h _ hs
    have hsH : √C / √H * H = √(H * C) := by
      rw [Real.sqrt_mul hH, div_mul_eq_mul_div, div_eq_iff (Real.sqrt_pos.2 hHp).ne']
      rw [show H = √H * √H from (Real.mul_self_sqrt hH).symm]
      rw [Real.sqrt_mul_self (Real.sqrt_nonneg H)]
      ring
    have hCs : C / (√C / √H) = √(H * C) := by
      rw [Real.sqrt_mul hH, div_div_eq_mul_div, div_eq_iff (Real.sqrt_pos.2 hCp).ne']
      rw [show C = √C * √C from (Real.mul_self_sqrt hC).symm]
      rw [Real.sqrt_mul_self (Real.sqrt_nonneg C)]
      ring
    rw [hsH, hCs] at h1
    linarith

/-- The quadratic step: `Q² ≤ V(RQ + VE)` gives `Q ≤ (R + √E)V`. -/
lemma quad_step {Q R E V : ℝ} (_hQ : 0 ≤ Q) (hR : 0 ≤ R) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (h : Q ^ 2 ≤ V * (R * Q + V * E)) : Q ≤ (R + √E) * V := by
  by_contra hcon
  push Not at hcon
  have hs := Real.sqrt_nonneg E
  have hs2 : √E ^ 2 = E := Real.sq_sqrt hE
  have hQp : 0 < Q := lt_of_le_of_lt (by positivity) hcon
  have h1 : Q * ((R + √E) * V) < Q * Q := mul_lt_mul_of_pos_left hcon hQp
  have h2 : √E * V * ((R + √E) * V) ≤ √E * V * Q :=
    mul_le_mul_of_nonneg_left hcon.le (by positivity)
  have h3 : 0 ≤ √E * R * (V * V) := mul_nonneg (mul_nonneg hs hR) (mul_nonneg hV hV)
  have e1 : Q * ((R + √E) * V) = R * Q * V + √E * V * Q := by ring
  have e2 : √E * V * ((R + √E) * V) = √E * R * (V * V) + √E ^ 2 * (V * V) := by ring
  rw [hs2] at e2
  have e3 : V * (R * Q + V * E) = R * Q * V + E * (V * V) := by ring
  nlinarith

end scalar

section abstract

variable {X : Type*} [MeasurableSpace X] {m k : ℕ}

/-- **The weighted Schur test** (abstract form of paper Lemmas `t7:p04:dual`, `t7:p04:schur`,
`t7:p04:MS`): for `Q(v) = ∫ w |vᵀB|²`, a kernel bound `|⟨B u, B' u'⟩| ≤ κ |u||u'|` on a
symmetric pair set `G` with row integrals `∫ 1_G κ w' ≤ R`, and the exceptional mass
`H = μ⊗μ(Gᶜ ∩ S×S)` (`w = 0` off `S`): `Q(v) ≤ (R + √(√H·∫ w² β⁴))·|v|²`, `β ≥ ‖B‖_op`. -/
theorem schur_abstract (μ : Measure X) [IsProbabilityMeasure μ]
    (B : X → Matrix (Fin m) (Fin k) ℝ) (hB : ∀ i j, Measurable (fun ξ => B ξ i j))
    (β : X → ℝ) (hβm : Measurable β) (hβ : ∀ ξ, opN (B ξ) ≤ β ξ) {CB : ℝ}
    (hCB : ∀ ξ, β ξ ≤ CB)
    (w : X → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ) (hwi : Integrable w μ)
    (hw2 : Integrable (fun ξ => w ξ ^ 2) μ) (S : Set X) (hS : MeasurableSet S)
    (hwS : ∀ ξ, ξ ∉ S → w ξ = 0)
    (κ : X → X → ℝ) (hκm : Measurable (Function.uncurry κ)) (hκ0 : ∀ a b, 0 ≤ κ a b)
    (hκs : ∀ a b, κ a b = κ b a) {K : ℝ} (hκK : ∀ a b, κ a b ≤ K)
    (G : Set (X × X)) (hG : MeasurableSet G) (hGs : ∀ a b, (a, b) ∈ G → (b, a) ∈ G)
    (hpair : ∀ a b, (a, b) ∈ G → ∀ u u' : Fin k → ℝ,
      |(B a *ᵥ u) ⬝ᵥ (B b *ᵥ u')| ≤ κ a b * nrm u * nrm u')
    {R : ℝ} (hrow : ∀ ξ, ∫ ξ', G.indicator (Function.uncurry κ) (ξ, ξ') * w ξ' ∂μ ≤ R)
    (v : Fin m → ℝ) :
    ∫ ξ, w ξ * normSq (vecMul v (B ξ)) ∂μ ≤
      (R + √(√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) * ∫ ξ, w ξ ^ 2 * β ξ ^ 4 ∂μ)) * normSq v := by
  classical
  set f : X → Fin k → ℝ := fun ξ => vecMul v (B ξ) with hfd
  set g : X → Fin m → ℝ := fun ξ => w ξ • (B ξ *ᵥ f ξ) with hgd
  set V := normSq v with hVd
  have hV0 : 0 ≤ V := normSq_nonneg v
  have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ => (opN_nonneg _).trans (hβ ξ)
  -- measurability
  have hfm : ∀ j, Measurable (fun ξ => f ξ j) := by
    intro j
    show Measurable (fun ξ => ∑ i, v i * B ξ i j)
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hB i j)
  have hBfm : ∀ i, Measurable (fun ξ => (B ξ *ᵥ f ξ) i) := by
    intro i
    show Measurable (fun ξ => ∑ j, B ξ i j * f ξ j)
    exact Finset.measurable_sum _ fun j _ => (hB i j).mul (hfm j)
  have hgm : ∀ i, Measurable (fun ξ => g ξ i) := fun i => hwm.mul (hBfm i)
  have hnfm : Measurable (fun ξ => normSq (f ξ)) := by
    show Measurable (fun ξ => ∑ j, f ξ j ^ 2)
    exact Finset.measurable_sum _ fun j _ => (hfm j).pow_const 2
  -- pointwise bounds
  have hfb : ∀ ξ, nrm (f ξ) ≤ β ξ * nrm v := fun ξ =>
    (nrm_vecMul_le _ _).trans (mul_le_mul_of_nonneg_right (hβ ξ) (nrm_nonneg _))
  have hBfb : ∀ ξ, nrm (B ξ *ᵥ f ξ) ≤ β ξ ^ 2 * nrm v := by
    intro ξ
    refine (nrm_mulVec_le _ _).trans ?_
    have := mul_le_mul (hβ ξ) (hfb ξ) (nrm_nonneg _) (hβ0 ξ)
    nlinarith [this]
  have hnf : ∀ ξ, normSq (f ξ) ≤ CB ^ 2 * V := by
    intro ξ
    rw [← nrm_sq, hVd, ← nrm_sq]
    have h1 := hfb ξ
    have h2 : β ξ * nrm v ≤ CB * nrm v := mul_le_mul_of_nonneg_right (hCB ξ) (nrm_nonneg _)
    have h3 : 0 ≤ nrm (f ξ) := nrm_nonneg _
    have h4 : 0 ≤ β ξ * nrm v := mul_nonneg (hβ0 ξ) (nrm_nonneg _)
    have h5 : nrm (f ξ) ^ 2 ≤ (CB * nrm v) ^ 2 := pow_le_pow_left₀ h3 (h1.trans h2) 2
    nlinarith
  have hgb : ∀ ξ, nrm (g ξ) ≤ w ξ * β ξ ^ 2 * nrm v := by
    intro ξ
    have e : nrm (g ξ) = w ξ * nrm (B ξ *ᵥ f ξ) := by
      show √(normSq (w ξ • (B ξ *ᵥ f ξ))) = _
      have : normSq (w ξ • (B ξ *ᵥ f ξ)) = w ξ ^ 2 * normSq (B ξ *ᵥ f ξ) := by
        simp [normSq, Finset.mul_sum, mul_pow]
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hw0 ξ)]
      rfl
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hBfb ξ) (hw0 ξ)
  have hgi : ∀ i, Integrable (fun ξ => g ξ i) μ := by
    intro i
    refine Integrable.mono' (hwi.mul_const (CB ^ 2 * nrm v)) (hgm i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_coord_le_nrm _ i).trans ((hgb ξ).trans ?_)
    have h1 : β ξ ^ 2 ≤ CB ^ 2 := pow_le_pow_left₀ (hβ0 ξ) (hCB ξ) 2
    have := mul_le_mul_of_nonneg_left h1 (hw0 ξ)
    have := mul_le_mul_of_nonneg_right this (nrm_nonneg v)
    linarith
  -- the identity `Q = v·a`, `a = ∫ g`
  set a : Fin m → ℝ := fun i => ∫ ξ, g ξ i ∂μ with had
  set Q := ∫ ξ, w ξ * normSq (vecMul v (B ξ)) ∂μ with hQd
  have hpt : ∀ ξ, w ξ * normSq (f ξ) = ∑ i, v i * g ξ i := by
    intro ξ
    have e1 : ∑ i, v i * g ξ i = w ξ * (v ⬝ᵥ (B ξ *ᵥ f ξ)) := by
      simp only [hgd, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, dotProduct_mulVec, normSq_eq_dot]
  have hQa : Q = v ⬝ᵥ a := by
    rw [hQd]
    have e : (fun ξ => w ξ * normSq (vecMul v (B ξ))) = fun ξ => ∑ i, v i * g ξ i :=
      funext hpt
    rw [e, integral_finsetSum _ fun i _ => (hgi i).const_mul (v i)]
    simp only [dotProduct, had]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hQ0 : 0 ≤ Q := integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (normSq_nonneg _)
  have hQ2 : Q ^ 2 ≤ V * normSq a := by
    have h1 : Q ≤ nrm v * nrm a := hQa ▸ (le_abs_self _).trans (abs_dot_le_nrm v a)
    have h2 := pow_le_pow_left₀ hQ0 h1 2
    rw [mul_pow, nrm_sq, nrm_sq] at h2
    exact h2
  -- `|a|² = ∫∫ g·g'`
  have hpi : Integrable (fun p : X × X => g p.1 ⬝ᵥ g p.2) (μ.prod μ) := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hgi i).mul_prod (hgi i)
  have haP : normSq a = ∫ p, g p.1 ⬝ᵥ g p.2 ∂(μ.prod μ) := by
    simp only [dotProduct]
    rw [integral_finsetSum _ fun i _ => (hgi i).mul_prod (hgi i)]
    simp only [normSq, had]
    exact Finset.sum_congr rfl fun i _ => by
      rw [integral_prod_mul (fun ξ => g ξ i) (fun ξ => g ξ i), sq]
  -- the kernel, the weights of the bad pairs
  set kG : X × X → ℝ := G.indicator (Function.uncurry κ) with hkGd
  have hkGm : Measurable kG := hκm.indicator hG
  have hkG0 : ∀ p, 0 ≤ kG p := fun p => Set.indicator_nonneg (fun q _ => hκ0 q.1 q.2) p
  have hkGK : ∀ p, kG p ≤ K := by
    intro p
    by_cases hp : p ∈ G
    · rw [hkGd, Set.indicator_of_mem hp]; exact hκK _ _
    · rw [hkGd, Set.indicator_of_notMem hp]; exact (hκ0 p.1 p.2).trans (hκK _ _)
  have hkGs : ∀ p : X × X, kG p.swap = kG p := by
    intro p
    by_cases hp : p ∈ G
    · have hp' : p.swap ∈ G := hGs _ _ hp
      rw [hkGd, Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      exact hκs _ _
    · have hp' : p.swap ∉ G := fun h => hp (hGs _ _ h)
      rw [hkGd, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  set F : X → ℝ := fun ξ => w ξ * β ξ ^ 2 with hFd
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => mul_nonneg (hw0 ξ) (sq_nonneg _)
  set ind : X × X → ℝ := (Gᶜ ∩ S ×ˢ S).indicator 1 with hindd
  set T1 : X × X → ℝ := fun p => kG p * (w p.1 * normSq (f p.1) * w p.2) / 2 with hT1d
  set Bd : X × X → ℝ := fun p => ind p * (F p.1 * F p.2) with hBdd
  -- the pointwise bound
  have hptb : ∀ p : X × X, g p.1 ⬝ᵥ g p.2 ≤ T1 p + T1 p.swap + V * Bd p := by
    intro p
    have hT1s : T1 p.swap = kG p * (w p.2 * normSq (f p.2) * w p.1) / 2 := by
      simp only [hT1d, Prod.fst_swap, Prod.snd_swap, hkGs]
    have hT1p : T1 p = kG p * (w p.1 * normSq (f p.1) * w p.2) / 2 := rfl
    rw [hT1s]
    by_cases hp : p ∈ G
    · have hBd0 : Bd p = 0 := by
        have hn : p ∉ Gᶜ ∩ S ×ˢ S := fun h => h.1 hp
        simp only [hBdd, hindd, Set.indicator_of_notMem hn, zero_mul]
      rw [hT1p, hBd0, hkGd, Set.indicator_of_mem hp]
      have e : g p.1 ⬝ᵥ g p.2 = w p.1 * w p.2 * ((B p.1 *ᵥ f p.1) ⬝ᵥ (B p.2 *ᵥ f p.2)) := by
        simp only [hgd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
      rw [e]
      have h1 := (le_abs_self _).trans (hpair p.1 p.2 (by simpa using hp) (f p.1) (f p.2))
      have hww : 0 ≤ w p.1 * w p.2 := mul_nonneg (hw0 _) (hw0 _)
      have h2 := mul_le_mul_of_nonneg_left h1 hww
      have h3 : 2 * (nrm (f p.1) * nrm (f p.2)) ≤ normSq (f p.1) + normSq (f p.2) := by
        rw [← nrm_sq, ← nrm_sq]; nlinarith [sq_nonneg (nrm (f p.1) - nrm (f p.2))]
      have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (hκ0 p.1 p.2) hww)
      have hu : Function.uncurry κ p = κ p.1 p.2 := rfl
      rw [hu]
      nlinarith
    · have hkG0' : kG p = 0 := by rw [hkGd, Set.indicator_of_notMem hp]
      have hT10 : T1 p = 0 := by simp only [hT1d, hkG0', zero_mul, zero_div]
      rw [hkG0', hT10]
      by_cases hSS : p ∈ S ×ˢ S
      swap
      · have hz : w p.1 * w p.2 = 0 := by
          rcases not_and_or.1 (by simpa [Set.mem_prod] using hSS) with h | h
          · rw [hwS _ h, zero_mul]
          · rw [hwS _ h, mul_zero]
        have e : g p.1 ⬝ᵥ g p.2 = w p.1 * w p.2 * ((B p.1 *ᵥ f p.1) ⬝ᵥ (B p.2 *ᵥ f p.2)) := by
          simp only [hgd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
        have hB0 : 0 ≤ Bd p := mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) p)
          (mul_nonneg (hF0 _) (hF0 _))
        rw [e, hz, zero_mul]
        simp only [zero_mul, zero_div, zero_add]
        exact mul_nonneg hV0 hB0
      have hind : ind p = 1 := by
        simp only [hindd]; rw [Set.indicator_of_mem (show p ∈ Gᶜ ∩ S ×ˢ S from ⟨hp, hSS⟩)]; rfl
      simp only [hBdd, hind, zero_mul, zero_div, one_mul, add_zero, zero_add]
      refine (le_abs_self _).trans ((abs_dot_le_nrm _ _).trans ?_)
      have h1 := hgb p.1
      have h2 := hgb p.2
      have e : V * (F p.1 * F p.2) = (w p.1 * β p.1 ^ 2 * nrm v) * (w p.2 * β p.2 ^ 2 * nrm v) := by
        rw [hVd, ← nrm_sq, hFd]; ring
      rw [e]
      exact mul_le_mul h1 h2 (nrm_nonneg _)
        (mul_nonneg (mul_nonneg (hw0 _) (sq_nonneg _)) (nrm_nonneg _))
  -- integrability
  have hww : Integrable (fun p : X × X => w p.1 * w p.2) (μ.prod μ) := hwi.mul_prod hwi
  have hwnf : Integrable (fun ξ => w ξ * normSq (f ξ)) μ := by
    refine Integrable.mono' (hwi.mul_const (CB ^ 2 * V)) (hwm.mul hnfm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 ξ) (normSq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hnf ξ) (hw0 ξ)
  have hT1m : Measurable T1 :=
    (hkGm.mul (((hwm.comp measurable_fst).mul (hnfm.comp measurable_fst)).mul
      (hwm.comp measurable_snd))).div_const 2
  have hT1i : Integrable T1 (μ.prod μ) := by
    refine Integrable.mono' (hww.const_mul (K * (CB ^ 2 * V) / 2)) hT1m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have hK0 : 0 ≤ K := (hkG0 p).trans (hkGK p)
    have h1 : 0 ≤ w p.1 * normSq (f p.1) * w p.2 :=
      mul_nonneg (mul_nonneg (hw0 _) (normSq_nonneg _)) (hw0 _)
    have h0 : 0 ≤ T1 p := div_nonneg (mul_nonneg (hkG0 p) h1) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have h2 : w p.1 * normSq (f p.1) * w p.2 ≤ w p.1 * (CB ^ 2 * V) * w p.2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hnf _) (hw0 _)) (hw0 _)
    have h3 := mul_le_mul (hkGK p) h2 h1 hK0
    show kG p * (w p.1 * normSq (f p.1) * w p.2) / 2 ≤ K * (CB ^ 2 * V) / 2 * (w p.1 * w p.2)
    nlinarith
  have hT1si : Integrable (fun p : X × X => T1 p.swap) (μ.prod μ) := hT1i.swap
  have hFm : Measurable F := hwm.mul (hβm.pow_const 2)
  have hindm : Measurable ind := measurable_const.indicator (hG.compl.inter (hS.prod hS))
  have hind01 : ∀ p, ind p = 0 ∨ ind p = 1 := by
    intro p
    by_cases hp : p ∈ Gᶜ ∩ S ×ˢ S
    · right; simp only [hindd]; rw [Set.indicator_of_mem hp]; rfl
    · left; simp only [hindd]; rw [Set.indicator_of_notMem hp]
  have hBdi : Integrable Bd (μ.prod μ) := by
    refine Integrable.mono' (hww.const_mul (CB ^ 4)) (hindm.mul ((hFm.comp measurable_fst).mul
      (hFm.comp measurable_snd))).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hFF : 0 ≤ F p.1 * F p.2 := mul_nonneg (hF0 _) (hF0 _)
    have hb1 : β p.1 ^ 2 ≤ CB ^ 2 := pow_le_pow_left₀ (hβ0 _) (hCB _) 2
    have hb2 : β p.2 ^ 2 ≤ CB ^ 2 := pow_le_pow_left₀ (hβ0 _) (hCB _) 2
    have hF1 : F p.1 ≤ w p.1 * CB ^ 2 := mul_le_mul_of_nonneg_left hb1 (hw0 _)
    have hF2 : F p.2 ≤ w p.2 * CB ^ 2 := mul_le_mul_of_nonneg_left hb2 (hw0 _)
    have h3 : F p.1 * F p.2 ≤ (w p.1 * CB ^ 2) * (w p.2 * CB ^ 2) :=
      mul_le_mul hF1 hF2 (hF0 _) (mul_nonneg (hw0 _) (sq_nonneg _))
    have hval : ‖Bd p‖ ≤ F p.1 * F p.2 := by
      rcases hind01 p with h | h
      · simp only [hBdd, h, zero_mul, norm_zero]; exact hFF
      · simp only [hBdd, h, one_mul]; rw [Real.norm_eq_abs, abs_of_nonneg hFF]
    exact hval.trans (h3.trans (le_of_eq (by ring)))
  -- the main pair integral
  have hP : ∫ p, g p.1 ⬝ᵥ g p.2 ∂(μ.prod μ) ≤
      ∫ p, T1 p ∂(μ.prod μ) + ∫ p, T1 p.swap ∂(μ.prod μ) + V * ∫ p, Bd p ∂(μ.prod μ) := by
    have e1 : ∫ p, (T1 p + T1 p.swap + V * Bd p) ∂(μ.prod μ) = ∫ p, T1 p ∂(μ.prod μ) +
        ∫ p, T1 p.swap ∂(μ.prod μ) + V * ∫ p, Bd p ∂(μ.prod μ) := by
      have hS : Integrable (fun p : X × X => T1 p + T1 p.swap) (μ.prod μ) := hT1i.add hT1si
      rw [integral_add (f := fun p => T1 p + T1 p.swap) (g := fun p => V * Bd p) hS
        (hBdi.const_mul V), integral_add (f := T1) (g := fun p => T1 p.swap) hT1i hT1si,
        integral_const_mul]
    rw [← e1]
    exact integral_mono hpi (f := fun p => g p.1 ⬝ᵥ g p.2)
      (g := fun p => T1 p + T1 p.swap + V * Bd p) ((hT1i.add hT1si).add (hBdi.const_mul V)) hptb
  rw [integral_prod_swap T1] at hP
  -- the good pairs: the row bound
  have hR0 : 0 ≤ R := by
    have := nonempty_of_isProbabilityMeasure μ
    obtain ⟨ξ⟩ := this
    refine le_trans ?_ (hrow ξ)
    exact integral_nonneg fun ξ' => mul_nonneg (hkG0 _) (hw0 _)
  have hT1b : ∫ p, T1 p ∂(μ.prod μ) ≤ R * Q / 2 := by
    rw [integral_prod T1 hT1i]
    have e : ∀ x, ∫ y, T1 (x, y) ∂μ =
        (w x * normSq (f x) / 2) * ∫ y, kG (x, y) * w y ∂μ := by
      intro x
      rw [← integral_const_mul]
      congr 1; funext y
      show kG (x, y) * (w x * normSq (f x) * w y) / 2 = _
      ring
    simp_rw [e]
    have hRi : Integrable (fun x => (w x * normSq (f x) / 2) * R) μ :=
      (hwnf.div_const 2).mul_const R
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) hRi
      (Filter.Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
    · exact mul_nonneg (div_nonneg (mul_nonneg (hw0 x) (normSq_nonneg _)) (by norm_num))
        (integral_nonneg fun y => mul_nonneg (hkG0 _) (hw0 _))
    · exact mul_le_mul_of_nonneg_left (hrow x)
        (div_nonneg (mul_nonneg (hw0 x) (normSq_nonneg _)) (by norm_num))
    · rw [integral_mul_const, integral_div, hQd]
      ring
  -- the bad pairs
  set H := (μ.prod μ).real (Gᶜ ∩ S ×ˢ S) with hHd
  set A := ∫ ξ, w ξ ^ 2 * β ξ ^ 4 ∂μ with hAd
  have hH0 : 0 ≤ H := measureReal_nonneg
  have hF2 : ∀ ξ, F ξ ^ 2 = w ξ ^ 2 * β ξ ^ 4 := fun ξ => by simp only [hFd]; ring
  have hF2i : Integrable (fun ξ => F ξ ^ 2) μ := by
    refine Integrable.mono' (hw2.mul_const (CB ^ 4)) (hFm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hF2]
    have : β ξ ^ 4 ≤ CB ^ 4 := pow_le_pow_left₀ (hβ0 _) (hCB _) 4
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hA0 : 0 ≤ A := integral_nonneg fun ξ => by positivity
  have hFFi : ∫ p, F p.1 ^ 2 * F p.2 ^ 2 ∂(μ.prod μ) = A * A := by
    rw [integral_prod_mul (fun ξ => F ξ ^ 2) (fun ξ => F ξ ^ 2)]
    simp only [hF2, hAd]
  have hindi : ∫ p, ind p ∂(μ.prod μ) = H := integral_indicator_one (hG.compl.inter (hS.prod hS))
  have hJ : ∫ p, Bd p ∂(μ.prod μ) ≤ √H * A := by
    have h := le_sqrt_of_forall_pos (J := ∫ p, Bd p ∂(μ.prod μ)) hH0 (mul_nonneg hA0 hA0)
      (fun s hs => by
        have hint : Integrable (fun p : X × X => (s * ind p + F p.1 ^ 2 * F p.2 ^ 2 / s) / 2)
            (μ.prod μ) := by
          have hi1 : Integrable ind (μ.prod μ) :=
            (integrable_const (1 : ℝ)).indicator (hG.compl.inter (hS.prod hS))
          exact ((hi1.const_mul s).add ((hF2i.mul_prod hF2i).div_const s)).div_const 2
        have hle : ∫ p, Bd p ∂(μ.prod μ) ≤
            ∫ p, (s * ind p + F p.1 ^ 2 * F p.2 ^ 2 / s) / 2 ∂(μ.prod μ) := by
          refine integral_mono hBdi hint fun p => ?_
          have hFF : 0 ≤ F p.1 * F p.2 := mul_nonneg (hF0 _) (hF0 _)
          have hsq : 0 ≤ (s - F p.1 * F p.2) ^ 2 := sq_nonneg _
          show ind p * (F p.1 * F p.2) ≤ _
          rcases hind01 p with h | h
          · rw [h]; simp only [zero_mul, mul_zero, zero_add]; positivity
          · rw [h, one_mul, mul_one]
            rw [show F p.1 ^ 2 * F p.2 ^ 2 = (F p.1 * F p.2) ^ 2 by ring]
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            have : (F p.1 * F p.2) ^ 2 / s = (F p.1 * F p.2) ^ 2 * s⁻¹ := div_eq_mul_inv _ _
            have hs' : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
            have : (F p.1 * F p.2) * 2 ≤ s + (F p.1 * F p.2) ^ 2 / s := by
              rw [← sub_nonneg]
              have e : s + (F p.1 * F p.2) ^ 2 / s - F p.1 * F p.2 * 2 =
                  (s - F p.1 * F p.2) ^ 2 / s := by field_simp; ring
              rw [e]; positivity
            linarith
        refine hle.trans (le_of_eq ?_)
        have hi1 : Integrable ind (μ.prod μ) :=
          (integrable_const (1 : ℝ)).indicator (hG.compl.inter (hS.prod hS))
        rw [integral_div, integral_add (f := fun p => s * ind p)
          (g := fun p => F p.1 ^ 2 * F p.2 ^ 2 / s) (hi1.const_mul s)
          ((hF2i.mul_prod hF2i).div_const s), integral_const_mul, integral_div, hFFi, hindi])
    refine h.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hH0, Real.sqrt_mul_self hA0]
  -- conclusion
  have hfin : Q ^ 2 ≤ V * (R * Q + V * (√H * A)) := by
    refine hQ2.trans ?_
    rw [haP]
    refine mul_le_mul_of_nonneg_left ?_ hV0
    have := mul_le_mul_of_nonneg_left hJ hV0
    linarith
  exact quad_step hQ0 hR0 (mul_nonneg (Real.sqrt_nonneg _) hA0) hV0 hfin

end abstract
end BstLean.Part182

open BstLean.Part182 in
#print axioms schur_abstract
open BstLean.Part182 in
#print axioms pair_of_opN
