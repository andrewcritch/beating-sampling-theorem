import BstLean.Part86Defs
import BstLean.Part84Rep
import BstLean.Part84Decor

/-!
# Part 86: slice decorrelation (`decor86 : Decor86 M Lam`)

In every slice `p`, `Var_W(E_g F) ≤ Λ E_g Var_W F`. The slice distribution is moved to
`ν = γ.map (X(p, ·))`, a probability measure on the unit ball; then the proof is Part 84's
decorrelation proof with an `x`-dependent polynomial: `F_x(W) = Σ_k β_k(x) h_{A_k}(lam W ψ(x))`
with fixed symmetric families `A_k` and continuous `β_k`.
-/

namespace BstLean.Part86

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (frob Tens IsSymmT)
open BstLean.Part53 (heatA tinner fvA)
open BstLean.Part59 (tensOf)
open BstLean.Part78 (zv Good good_coord sep_int sep_swap sep_swap_two)
open BstLean.Part84 (var_expand)
open BstLean.Part84.Rep (cOf polyEval_cOf unitT unitT_symm fvA_unitT heat_unitT_pos heat_unitT_zero
  tinner_zero_order)

namespace Dec

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-! ## Measures on the unit ball -/

lemma cube_of_ball {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 ≤ 1) :
    x ∈ Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    nlinarith [sq_nonneg (x i - 1)]

lemma bint {ν : Measure (Fin n → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, ∑ i, x i ^ 2 ≤ 1) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f ν := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hν] with x hx
  apply hC
  exact Set.mem_image_of_mem _ (cube_of_ball hx)

lemma prod_int {ν : Measure (Fin n → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, ∑ i, x i ^ 2 ≤ 1) {φ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hφ : Continuous φ) :
    Integrable φ (ν.prod ν) := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ)) (b := fun _ => (1 : ℝ))).prod
    (isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ)) (b := fun _ => (1 : ℝ)))).bddAbove_image
      hφ.norm.continuousOn
  apply Integrable.of_bound hφ.aestronglyMeasurable C
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,
    Measure.quasiMeasurePreserving_snd.ae hν] with z h1 h2
  apply hC
  exact Set.mem_image_of_mem _ ⟨cube_of_ball h1, cube_of_ball h2⟩

lemma prod_split {ν : Measure (Fin n → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, ∑ i, x i ^ 2 ≤ 1) {m : (Fin n → ℝ) → ℝ}
    {R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hm : Continuous m) (hR : Continuous R) :
    ∫ x, ∫ y, (m x * m y + R (x, y)) ∂ν ∂ν = (∫ x, m x ∂ν) ^ 2 + ∫ z, R z ∂(ν.prod ν) := by
  have hmm : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => m z.1 * m z.2) :=
    (hm.comp continuous_fst).mul (hm.comp continuous_snd)
  have i1 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => m z.1 * m z.2) (ν.prod ν) :=
    prod_int hν hmm
  have i2 : Integrable R (ν.prod ν) := prod_int hν hR
  have e := integral_prod (fun z : (Fin n → ℝ) × (Fin n → ℝ) => m z.1 * m z.2 + R z) (i1.add i2)
  have e2 := integral_add i1 i2
  have e3 := integral_prod_mul (μ := ν) (ν := ν) m m
  simp only at e
  rw [← e, e2, e3, sq]

/-! ## The features and the kernel -/

lemma cont_ps (M : Mod n I J S G) (q : J) : Continuous (fun x : Fin n → ℝ => M.ps x q) := by
  unfold Mod.ps
  exact MvPolynomial.continuous_eval _

lemma cont_b (M : Mod n I J S G) (j : I) : Continuous (fun x : Fin n → ℝ => M.b x j) := by
  unfold Mod.b
  exact MvPolynomial.continuous_eval _

lemma cont_kap2 (M : Mod n I J S G) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kapm M z.1 z.2) :=
  continuous_finsetSum _ fun q _ =>
    ((cont_ps M q).comp continuous_fst).mul ((cont_ps M q).comp continuous_snd)

lemma cont_kap_diag (M : Mod n I J S G) : Continuous (fun x : Fin n → ℝ => kapm M x x) :=
  continuous_finsetSum _ fun q _ => (cont_ps M q).mul (cont_ps M q)

lemma kap_nonneg (M : Mod n I J S G) (x : Fin n → ℝ) : 0 ≤ kapm M x x :=
  Finset.sum_nonneg fun q _ => mul_self_nonneg _

lemma kap_symm (M : Mod n I J S G) (x y : Fin n → ℝ) : kapm M x y = kapm M y x :=
  Finset.sum_congr rfl fun q _ => mul_comm _ _

lemma kap_diag (M : Mod n I J S G) (x : Fin n → ℝ) : kapm M x x = ∑ q, M.ps x q ^ 2 :=
  Finset.sum_congr rfl fun q _ => (sq _).symm

lemma kap_cs (M : Mod n I J S G) (x y : Fin n → ℝ) :
    kapm M x y ^ 2 ≤ kapm M x x * kapm M y y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
    (fun q => M.ps x q) (fun q => M.ps y q)
  rw [kap_diag M x, kap_diag M y]
  exact h

/-! ## The slice hypotheses on `ν` -/

/-- The slice hypotheses, on the image measure. -/
structure SliceH (M : Mod n I J S G) (ν : Measure (Fin n → ℝ)) (Lam τ : ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  ball : ∀ᵐ x ∂ν, ∑ i, x i ^ 2 ≤ 1
  lam0 : 0 ≤ Lam
  tau0 : 0 ≤ τ
  tau : ∀ᵐ x ∂ν, τ ≤ kapm M x x
  op : ∀ c : J → ℝ, ∫ x, (∑ q, c q * M.ps x q) ^ 2 ∂ν ≤ Lam * τ * ∑ q, c q ^ 2

lemma kap2_int {M : Mod n I J S G} {ν : Measure (Fin n → ℝ)} {Lam τ : ℝ}
    (h : SliceH M ν Lam τ) (x : Fin n → ℝ) :
    ∫ y, kapm M x y ^ 2 ∂ν ≤ Lam * τ * kapm M x x := by
  have h1 := h.op (fun q => M.ps x q)
  rw [← kap_diag M x] at h1
  exact h1

lemma diag_step {M : Mod n I J S G} {ν : Measure (Fin n → ℝ)} {Lam τ : ℝ}
    (h : SliceH M ν Lam τ) {u : (Fin n → ℝ) → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, 0 ≤ u x) (j : ℕ) :
    τ * ∫ x, u x * kapm M x x ^ j ∂ν ≤ ∫ x, u x * kapm M x x ^ (j + 1) ∂ν := by
  have := h.prob
  rw [← integral_const_mul]
  apply integral_mono_ae ((bint h.ball (hu.mul ((cont_kap_diag M).pow j))).const_mul _)
    (bint h.ball (hu.mul ((cont_kap_diag M).pow (j + 1))))
  filter_upwards [h.tau] with x hx
  have hk0 : 0 ≤ kapm M x x := kap_nonneg M x
  show τ * (u x * kapm M x x ^ j) ≤ u x * kapm M x x ^ (j + 1)
  have := mul_le_mul_of_nonneg_left hx (mul_nonneg (hu0 x) (pow_nonneg hk0 j))
  rw [pow_succ, ← mul_assoc]
  linarith

/-! ## Bessel form of the slice feature operator bound -/

lemma bessel {M : Mod n I J S G} {ν : Measure (Fin n → ℝ)} {Lam τ : ℝ}
    (h : SliceH M ν Lam τ) {r : (Fin n → ℝ) → ℝ} (hr : Continuous r) :
    ∑ q : J, (∫ x, r x * M.ps x q ∂ν) ^ 2 ≤ Lam * τ * ∫ x, r x ^ 2 ∂ν := by
  have := h.prob
  have hν := h.ball
  obtain ⟨c, hc⟩ : ∃ c : J → ℝ, ∀ q, c q = ∫ x, r x * M.ps x q ∂ν := ⟨_, fun _ => rfl⟩
  simp_rw [← hc]
  obtain ⟨L, hL⟩ : ∃ L : (Fin n → ℝ) → ℝ, ∀ x, L x = ∑ q, c q * M.ps x q := ⟨_, fun _ => rfl⟩
  have hLc : Continuous L := by
    have : L = fun x => ∑ q, c q * M.ps x q := funext hL
    rw [this]
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (cont_ps M q)
  obtain ⟨Sq, hS⟩ : ∃ Sq : ℝ, Sq = ∑ q, c q ^ 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∫ x, r x ^ 2 ∂ν := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∫ x, L x ^ 2 ∂ν := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Lam * τ := ⟨_, rfl⟩
  rw [← hS, ← hR, ← ha]
  have hQa : Q ≤ a * Sq := by
    rw [hQ, ha, hS]
    simp_rw [hL]
    exact h.op c
  have hS0 : 0 ≤ Sq := by rw [hS]; exact Finset.sum_nonneg fun q _ => sq_nonneg _
  have hR0 : 0 ≤ R := by rw [hR]; exact integral_nonneg fun x => sq_nonneg _
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact integral_nonneg fun x => sq_nonneg _
  have hrp : ∀ q : J, Integrable (fun x => r x * M.ps x q) ν :=
    fun q => bint hν (hr.mul (cont_ps M q))
  have hr2 : Integrable (fun x => r x ^ 2) ν := bint hν (hr.pow 2)
  have hrL : Integrable (fun x => r x * L x) ν := bint hν (hr.mul hLc)
  have hL2 : Integrable (fun x => L x ^ 2) ν := bint hν (hLc.pow 2)
  have hcross : ∫ x, r x * L x ∂ν = Sq := by
    have h' : ∀ x, r x * L x = ∑ q, c q * (r x * M.ps x q) := by
      intro x
      rw [hL, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    simp_rw [h']
    rw [integral_finsetSum _ fun q _ => (hrp q).const_mul _]
    simp_rw [integral_const_mul, ← hc]
    rw [hS]
    exact Finset.sum_congr rfl fun q _ => by rw [sq]
  have key : ∀ t : ℝ, 0 ≤ R - 2 * t * Sq + t ^ 2 * Q := by
    intro t
    have h0 : 0 ≤ ∫ x, (r x - t * L x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have e : ∀ x, (r x - t * L x) ^ 2 = r x ^ 2 - (2 * t) * (r x * L x) + t ^ 2 * L x ^ 2 := by
      intro x; ring
    simp_rw [e] at h0
    have e1 := integral_add (hr2.sub (hrL.const_mul (2 * t))) (hL2.const_mul (t ^ 2))
    have e2 := integral_sub hr2 (hrL.const_mul (2 * t))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const_mul, hcross, ← hR, ← hQ] at h0
    exact h0
  have ha0 : 0 ≤ a := by rw [ha]; exact mul_nonneg h.lam0 h.tau0
  rcases ha0.eq_or_lt with h' | h'
  · rw [← h', zero_mul] at hQa ⊢
    by_contra hcon
    rw [not_le] at hcon
    have hk := key ((R + 1) / Sq)
    have hQ' : Q = 0 := le_antisymm hQa hQ0
    rw [hQ', mul_zero, add_zero, mul_assoc, div_mul_cancel₀ _ hcon.ne'] at hk
    linarith
  · have hk := key (1 / a)
    have h2 : (1 / a) ^ 2 * Q ≤ (1 / a) * Sq := by
      have h3 : (1 / a) ^ 2 * Q ≤ (1 / a) ^ 2 * (a * Sq) :=
        mul_le_mul_of_nonneg_left hQa (sq_nonneg _)
      have e : (1 / a) ^ 2 * (a * Sq) = 1 / a * Sq := by field_simp
      linarith
    have h3 : 0 ≤ R - 1 / a * Sq := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 h'.le
    have e : a * (R - 1 / a * Sq) = a * R - Sq := by field_simp
    linarith

/-! ## One chaos level -/

lemma term_bound {M : Mod n I J S G} {ν : Measure (Fin n → ℝ)} {Lam τ : ℝ}
    (h : SliceH M ν Lam τ) {I' : Type*} [Fintype I'] (Gf : I' → (Fin n → ℝ) → ℝ)
    (hG : ∀ w, Continuous (Gf w)) (c : ℕ) (hc : 1 ≤ c) :
    ∫ z, (∑ w, Gf w z.1 * Gf w z.2) * kapm M z.1 z.2 ^ c ∂(ν.prod ν) ≤
      Lam * ∫ x, (∑ w, Gf w x * Gf w x) * kapm M x x ^ c ∂ν := by
  have hprob := h.prob
  have hν := h.ball
  have hL := h.lam0
  have ha0 : 0 ≤ Lam * τ := mul_nonneg h.lam0 h.tau0
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ, ∀ x, f x = ∑ w, Gf w x * Gf w x := ⟨_, fun _ => rfl⟩
  have hfc : Continuous f := by
    have : f = fun x => ∑ w, Gf w x * Gf w x := funext hf
    rw [this]
    exact continuous_finsetSum _ fun w _ => (hG w).mul (hG w)
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    rw [hf]; exact Finset.sum_nonneg fun w _ => mul_self_nonneg _
  simp_rw [← hf]
  have hkc := cont_kap2 M
  have htc : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ∑ w, Gf w z.1 * Gf w z.2) :=
    continuous_finsetSum _ fun w _ =>
      ((hG w).comp continuous_fst).mul ((hG w).comp continuous_snd)
  obtain rfl | ⟨j, rfl⟩ : c = 1 ∨ ∃ j, c = j + 2 := by
    rcases c with _ | _ | j
    · omega
    · left; rfl
    · right; exact ⟨j, rfl⟩
  · -- the first chaos: Bessel
    have e1 : ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
        (∑ w, Gf w z.1 * Gf w z.2) * kapm M z.1 z.2 ^ 1 =
          ∑ w, ∑ q : J, (Gf w z.1 * M.ps z.1 q) * (Gf w z.2 * M.ps z.2 q) := by
      intro z
      rw [pow_one, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold kapm
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hi : ∀ (w : I') (q : J), Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (Gf w z.1 * M.ps z.1 q) * (Gf w z.2 * M.ps z.2 q))
        (ν.prod ν) := fun w q =>
      prod_int hν ((((hG w).mul (cont_ps M q)).comp continuous_fst).mul
        (((hG w).mul (cont_ps M q)).comp continuous_snd))
    simp_rw [e1]
    rw [integral_finsetSum _ fun w _ => integrable_finsetSum _ fun q _ => hi w q]
    have e2 : ∀ w, ∫ z : (Fin n → ℝ) × (Fin n → ℝ),
        ∑ q : J, (Gf w z.1 * M.ps z.1 q) * (Gf w z.2 * M.ps z.2 q) ∂(ν.prod ν) =
        ∑ q : J, (∫ x, Gf w x * M.ps x q ∂ν) ^ 2 := by
      intro w
      rw [integral_finsetSum _ fun q _ => hi w q]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [sq]
      exact integral_prod_mul (fun x => Gf w x * M.ps x q) (fun x => Gf w x * M.ps x q)
    simp_rw [e2]
    calc ∑ w, ∑ q : J, (∫ x, Gf w x * M.ps x q ∂ν) ^ 2
        ≤ ∑ w, Lam * τ * ∫ x, Gf w x ^ 2 ∂ν :=
          Finset.sum_le_sum fun w _ => bessel h (hG w)
      _ = Lam * (τ * ∫ x, f x * kapm M x x ^ 0 ∂ν) := by
          have hG2 : ∀ w, Integrable (fun x => Gf w x ^ 2) ν :=
            fun w => bint hν ((hG w).pow 2)
          rw [← Finset.mul_sum, ← integral_finsetSum _ fun w _ => hG2 w, mul_assoc]
          congr 2
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show ∑ w, Gf w x ^ 2 = f x * kapm M x x ^ 0
          rw [pow_zero, mul_one, hf]
          exact Finset.sum_congr rfl fun w _ => sq _
      _ ≤ Lam * ∫ x, f x * kapm M x x ^ (0 + 1) ∂ν :=
          mul_le_mul_of_nonneg_left (diag_step h hfc hf0 0) hL
      _ = _ := by rw [zero_add]
  · -- higher chaoses: Cauchy–Schwarz and the Hilbert–Schmidt bound
    obtain ⟨U, hU⟩ : ∃ U : (Fin n → ℝ) → ℝ, ∀ x, U x = f x * kapm M x x ^ j :=
      ⟨_, fun _ => rfl⟩
    have hUc : Continuous U := by
      have : U = fun x => f x * kapm M x x ^ j := funext hU
      rw [this]
      exact hfc.mul ((cont_kap_diag M).pow j)
    have hU0 : ∀ x, 0 ≤ U x := fun x => by
      rw [hU]; exact mul_nonneg (hf0 x) (pow_nonneg (kap_nonneg M x) j)
    have pw : ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
        (∑ w, Gf w z.1 * Gf w z.2) * kapm M z.1 z.2 ^ (j + 2) ≤
          1 / 2 * (kapm M z.1 z.2 ^ 2 * U z.1) + 1 / 2 * (kapm M z.2 z.1 ^ 2 * U z.2) := by
      rintro ⟨x, y⟩
      show (∑ w, Gf w x * Gf w y) * kapm M x y ^ (j + 2) ≤
        1 / 2 * (kapm M x y ^ 2 * U x) + 1 / 2 * (kapm M y x ^ 2 * U y)
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ∑ w, Gf w x * Gf w y := ⟨_, rfl⟩
      rw [← ht]
      have ht2 : t ^ 2 ≤ f x * f y := by
        have h' := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I')
          (fun w => Gf w x) (fun w => Gf w y)
        have e : ∀ z : Fin n → ℝ, f z = ∑ w, Gf w z ^ 2 := fun z => by
          rw [hf]; exact Finset.sum_congr rfl fun w _ => (sq _).symm
        rw [ht, e x, e y]
        exact h'
      have hk : kapm M x y ^ 2 ≤ kapm M x x * kapm M y y := kap_cs M x y
      have hsq : (t * kapm M x y ^ j) ^ 2 ≤ U x * U y := by
        calc (t * kapm M x y ^ j) ^ 2 = t ^ 2 * (kapm M x y ^ 2) ^ j := by ring
          _ ≤ (f x * f y) * (kapm M x x * kapm M y y) ^ j :=
              mul_le_mul ht2 (pow_le_pow_left₀ (sq_nonneg _) hk j)
                (pow_nonneg (sq_nonneg _) j) (mul_nonneg (hf0 x) (hf0 y))
          _ = U x * U y := by rw [hU, hU]; ring
      have h4 : (t * kapm M x y ^ j) ^ 2 ≤ ((U x + U y) / 2) ^ 2 := by
        nlinarith [sq_nonneg (U x - U y)]
      have h5 : t * kapm M x y ^ j ≤ (U x + U y) / 2 :=
        (abs_le_of_sq_le_sq' h4 (by have := hU0 x; have := hU0 y; linarith)).2
      rw [kap_symm M y x]
      calc t * kapm M x y ^ (j + 2) = (t * kapm M x y ^ j) * kapm M x y ^ 2 := by ring
        _ ≤ (U x + U y) / 2 * kapm M x y ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
        _ = _ := by ring
    have i1 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kapm M z.1 z.2 ^ 2 * U z.1)
        (ν.prod ν) :=
      prod_int hν ((hkc.pow 2).mul (hUc.comp continuous_fst))
    have i2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kapm M z.2 z.1 ^ 2 * U z.2)
        (ν.prod ν) := i1.swap
    have A1 : ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kapm M z.1 z.2 ^ 2 * U z.1 ∂(ν.prod ν) ≤
        Lam * τ * ∫ x, f x * kapm M x x ^ (j + 1) ∂ν := by
      rw [integral_prod _ i1]
      have h' : ∀ x : Fin n → ℝ, ∫ y, kapm M x y ^ 2 * U x ∂ν =
          U x * ∫ y, kapm M x y ^ 2 ∂ν := by
        intro x; rw [integral_mul_const, mul_comm]
      simp only [h']
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun x => mul_nonneg (hU0 x) (integral_nonneg fun y => sq_nonneg _)
      · exact (bint hν (hfc.mul ((cont_kap_diag M).pow (j + 1)))).const_mul _
      · refine ae_of_all _ fun x => ?_
        have h6 := mul_le_mul_of_nonneg_left (kap2_int h x) (hU0 x)
        calc U x * ∫ y, kapm M x y ^ 2 ∂ν
            ≤ U x * (Lam * τ * kapm M x x) := h6
          _ = Lam * τ * (f x * kapm M x x ^ (j + 1)) := by rw [hU]; ring
    have A2 : ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kapm M z.2 z.1 ^ 2 * U z.2 ∂(ν.prod ν) =
        ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kapm M z.1 z.2 ^ 2 * U z.1 ∂(ν.prod ν) :=
      integral_prod_swap (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kapm M z.1 z.2 ^ 2 * U z.1)
    calc ∫ z : (Fin n → ℝ) × (Fin n → ℝ), (∑ w, Gf w z.1 * Gf w z.2) * kapm M z.1 z.2 ^ (j + 2)
          ∂(ν.prod ν)
        ≤ ∫ z : (Fin n → ℝ) × (Fin n → ℝ),
            (1 / 2 * (kapm M z.1 z.2 ^ 2 * U z.1) + 1 / 2 * (kapm M z.2 z.1 ^ 2 * U z.2))
            ∂(ν.prod ν) :=
          integral_mono (prod_int hν (htc.mul (hkc.pow _)))
            ((i1.const_mul _).add (i2.const_mul _)) pw
      _ = 1 / 2 * ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kapm M z.1 z.2 ^ 2 * U z.1 ∂(ν.prod ν) +
          1 / 2 * ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kapm M z.2 z.1 ^ 2 * U z.2 ∂(ν.prod ν) := by
          rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ Lam * τ * ∫ x, f x * kapm M x x ^ (j + 1) ∂ν := by
          rw [A2]; linarith
      _ = Lam * (τ * ∫ x, f x * kapm M x x ^ (j + 1) ∂ν) := by ring
      _ ≤ Lam * ∫ x, f x * kapm M x x ^ (j + 1 + 1) ∂ν :=
          mul_le_mul_of_nonneg_left (diag_step h hfc hf0 (j + 1)) hL

/-! ## Separable form of `Fm` -/

/-- `F W x = Σ_k g_k(W) h_k(x)`, a finite sum, `g_k` with all moments, `h_k` continuous. -/
def Sep (F : (J × Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (g : ι → (J × Fin n → ℝ) → ℝ) (h : ι → (Fin n → ℝ) → ℝ),
    (∀ k, Good (stdGauss (J × Fin n)) (g k)) ∧ (∀ k, Continuous (h k)) ∧
    ∀ W x, F W x = ∑ k, g k W * h k x

lemma Sep.const (a : ℝ) : Sep (n := n) (J := J) (fun _ _ => a) :=
  ⟨Unit, inferInstance, fun _ _ => a, fun _ _ => 1, fun _ => Good.const a,
    fun _ => continuous_const, fun W x => by simp⟩

lemma Sep.add {F F' : (J × Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : Sep F) (hG : Sep F') :
    Sep (fun W x => F W x + F' W x) := by
  obtain ⟨ι, _, g, h, hg, hh, e⟩ := hF
  obtain ⟨ι', _, g', h', hg', hh', e'⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim g g', Sum.elim h h', ?_, ?_, ?_⟩
  · rintro (k | k)
    · exact hg k
    · exact hg' k
  · rintro (k | k)
    · exact hh k
    · exact hh' k
  · intro W x
    rw [Fintype.sum_sum_type]
    simp [e, e']

lemma Sep.mul {F F' : (J × Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : Sep F) (hG : Sep F') :
    Sep (fun W x => F W x * F' W x) := by
  obtain ⟨ι, _, g, h, hg, hh, e⟩ := hF
  obtain ⟨ι', _, g', h', hg', hh', e'⟩ := hG
  refine ⟨ι × ι', inferInstance, fun kl W => g kl.1 W * g' kl.2 W,
    fun kl x => h kl.1 x * h' kl.2 x, fun kl => (hg kl.1).mul (hg' kl.2),
    fun kl => (hh kl.1).mul (hh' kl.2), ?_⟩
  intro W x
  show F W x * F' W x = ∑ kl : ι × ι', (g kl.1 W * g' kl.2 W) * (h kl.1 x * h' kl.2 x)
  rw [e, e', Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma sep_Fm (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    Sep (Fm M P lam) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Fm M (MvPolynomial.C a) lam = fun _ _ => a := by
      funext W x; simp [Fm]
    rw [h]; exact Sep.const a
  | add p q hp hq =>
    have h : Fm M (p + q) lam = fun W x => Fm M p lam W x + Fm M q lam W x := by
      funext W x; simp [Fm]
    rw [h]; exact hp.add hq
  | mul_X p i hp =>
    rcases i with j | i
    · have h : Fm M (p * MvPolynomial.X (Sum.inl j)) lam =
          fun W x => Fm M p lam W x * M.b x j := by
        funext W x; simp [Fm]
      rw [h]
      refine hp.mul ⟨Unit, inferInstance, fun _ _ => 1, fun _ x => M.b x j,
        fun _ => Good.const 1, fun _ => cont_b M j, ?_⟩
      intro W x
      simp
    · have h : Fm M (p * MvPolynomial.X (Sum.inr i)) lam =
          fun W x => Fm M p lam W x * (lam * zv W (M.ps x) i) := by
        funext W x; simp [Fm]
      rw [h]
      refine hp.mul ⟨J, inferInstance, fun q W => lam * W (q, i), fun q x => M.ps x q,
        fun q => (good_coord (q, i)).const_mul lam, fun q => cont_ps M q, ?_⟩
      intro W x
      show lam * ∑ q : J, W (q, i) * M.ps x q = ∑ q : J, lam * W (q, i) * M.ps x q
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring

lemma sep_facts {ν : Measure (Fin n → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, ∑ i, x i ^ 2 ≤ 1)
    {F : (J × Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : Sep F) :
    (∀ W, Continuous (F W)) ∧
    (∀ x, Good (stdGauss (J × Fin n)) (fun W => F W x)) ∧
    Good (stdGauss (J × Fin n)) (fun W => ∫ x, F W x ∂ν) ∧
    ∫ W, ∫ x, F W x ∂ν ∂stdGauss (J × Fin n) =
      ∫ x, ∫ W, F W x ∂stdGauss (J × Fin n) ∂ν ∧
    ∫ W, (∫ x, F W x ∂ν) ^ 2 ∂stdGauss (J × Fin n) =
      ∫ x, ∫ y, ∫ W, F W x * F W y ∂stdGauss (J × Fin n) ∂ν ∂ν := by
  obtain ⟨ι, _, g, h, hg, hh, e⟩ := hF
  have hF : F = fun W x => ∑ k, g k W * h k x := by funext W x; exact e W x
  subst hF
  have hi : ∀ k, Integrable (h k) ν := fun k => bint hν (hh k)
  refine ⟨fun W => continuous_finsetSum _ fun k _ => continuous_const.mul (hh k),
    fun x => Good.sum _ fun k _ => (hg k).mul_const _, ?_, ?_, ?_⟩
  · simp_rw [sep_int g h hi]
    exact Good.sum _ fun k _ => (hg k).mul_const _
  · exact sep_swap g h (fun k => (hg k).integrable) hi
  · exact sep_swap_two g h (fun k l => ((hg k).mul (hg l)).integrable) hi

/-! ## The representation with fixed families -/

/-- `P(b(x), z) = Σ_k β_k(x) Q_k(z)`, `β_k` continuous. -/
lemma rep_poly (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (β : ι → (Fin n → ℝ) → ℝ) (Q : ι → MvPolynomial (Fin n) ℝ),
      (∀ k, Continuous (β k)) ∧ ∀ (x z : Fin n → ℝ),
        MvPolynomial.eval (Sum.elim (M.b x) z) P = ∑ k, β k x * MvPolynomial.eval z (Q k) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨Unit, inferInstance, fun _ _ => a, fun _ => 1, fun _ => continuous_const,
      fun x z => by simp⟩
  | add p q hp hq =>
    obtain ⟨ι, _, β, Q, hβ, e⟩ := hp
    obtain ⟨ι', _, β', Q', hβ', e'⟩ := hq
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim β β', Sum.elim Q Q', ?_, ?_⟩
    · rintro (k | k)
      · exact hβ k
      · exact hβ' k
    · intro x z
      rw [Fintype.sum_sum_type]
      simp [e, e']
  | mul_X p i hp =>
    obtain ⟨ι, _, β, Q, hβ, e⟩ := hp
    rcases i with j | i
    · refine ⟨ι, inferInstance, fun k x => β k x * M.b x j, Q,
        fun k => (hβ k).mul (cont_b M j), ?_⟩
      intro x z
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inl, e, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    · refine ⟨ι, inferInstance, β, fun k => Q k * MvPolynomial.X i, hβ, ?_⟩
      intro x z
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inr, e, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring

/-- One-point form of the two-point identity. -/
lemma onePt (hT : TwoPt n J) (K : ℕ) (A : Tens n) (hA : ∀ j, IsSymmT (A j)) (lam : ℝ)
    (p : J → ℝ) :
    Integrable (fun W : J × Fin n → ℝ => fvA K A (fun i => lam * zv W p i))
      (stdGauss (J × Fin n)) ∧
    ∫ W : J × Fin n → ℝ, fvA K A (fun i => lam * zv W p i) ∂stdGauss (J × Fin n) =
      heatA K (lam ^ 2 * ∑ q, p q ^ 2) A 0 (fun i => i.elim0) := by
  obtain ⟨hint, heq⟩ := hT K A (unitT n) hA unitT_symm lam p p
  simp only [fvA_unitT, mul_one] at hint heq
  refine ⟨hint, ?_⟩
  rw [heq, Finset.sum_eq_single 0]
  · rw [tinner_zero_order, heat_unitT_zero]
    simp
  · intro c _ hc
    rw [heat_unitT_pos K _ c hc]
    simp [tinner]
  · simp

/-! ## The chaos coefficients -/

section chaos

variable {ι : Type} [Fintype ι]

/-- The chaos coefficient of order `c` at `x`. -/
noncomputable def Gc (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ) (K : ℕ)
    (A : ι → Tens n) (c : ℕ) (w : Fin c → Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ k, β k x * heatA K (lam ^ 2 * kapm M x x) (A k) c w

/-- One level of the two-point function. -/
noncomputable def Tc (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ) (K : ℕ)
    (A : ι → Tens n) (c : ℕ) (x y : Fin n → ℝ) : ℝ :=
  (∑ w, Gc M lam β K A c w x * Gc M lam β K A c w y) * kapm M x y ^ c

/-- The covariance kernel. -/
noncomputable def Rr (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ) (K : ℕ)
    (A : ι → Tens n) (x y : Fin n → ℝ) : ℝ :=
  ∑ c ∈ Finset.range K, (((c + 1).factorial : ℝ) * lam ^ (2 * (c + 1))) *
    Tc M lam β K A (c + 1) x y

lemma cont_heatA (K : ℕ) (A : Tens n) (c : ℕ) (w : Fin c → Fin n) :
    Continuous (fun v : ℝ => heatA K v A c w) := by
  unfold heatA
  fun_prop

lemma cont_Gc (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ)
    (hβ : ∀ k, Continuous (β k)) (K : ℕ) (A : ι → Tens n) (c : ℕ) (w : Fin c → Fin n) :
    Continuous (Gc M lam β K A c w) := by
  unfold Gc
  exact continuous_finsetSum _ fun k _ => (hβ k).mul
    ((cont_heatA K (A k) c w).comp (continuous_const.mul (cont_kap_diag M)))

lemma cont_Tc (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ)
    (hβ : ∀ k, Continuous (β k)) (K : ℕ) (A : ι → Tens n) (c : ℕ) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Tc M lam β K A c z.1 z.2) := by
  unfold Tc
  exact (continuous_finsetSum _ fun w _ =>
    ((cont_Gc M lam β hβ K A c w).comp continuous_fst).mul
      ((cont_Gc M lam β hβ K A c w).comp continuous_snd)).mul ((cont_kap2 M).pow c)

lemma cont_Tc_diag (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ)
    (hβ : ∀ k, Continuous (β k)) (K : ℕ) (A : ι → Tens n) (c : ℕ) :
    Continuous (fun x : Fin n → ℝ => Tc M lam β K A c x x) := by
  unfold Tc
  exact (continuous_finsetSum _ fun w _ =>
    (cont_Gc M lam β hβ K A c w).mul (cont_Gc M lam β hβ K A c w)).mul ((cont_kap_diag M).pow c)

lemma gc_tinner (M : Mod n I J S G) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ) (K : ℕ)
    (A : ι → Tens n) (c : ℕ) (x y : Fin n → ℝ) :
    ∑ w, Gc M lam β K A c w x * Gc M lam β K A c w y =
      ∑ k, ∑ l, β k x * β l y *
        tinner (heatA K (lam ^ 2 * kapm M x x) (A k) c) (heatA K (lam ^ 2 * kapm M y y) (A l) c) := by
  unfold Gc tinner
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

lemma rr_bound {M : Mod n I J S G} {ν : Measure (Fin n → ℝ)} {Lam τ : ℝ}
    (h : SliceH M ν Lam τ) (lam : ℝ) (β : ι → (Fin n → ℝ) → ℝ)
    (hβ : ∀ k, Continuous (β k)) (K : ℕ) (A : ι → Tens n) :
    ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Rr M lam β K A z.1 z.2 ∂(ν.prod ν) ≤
      Lam * ∫ x, Rr M lam β K A x x ∂ν := by
  have hprob := h.prob
  have hd1 : ∀ c, Integrable (fun x : Fin n → ℝ => Tc M lam β K A c x x) ν :=
    fun c => bint h.ball (cont_Tc_diag M lam β hβ K A c)
  unfold Rr
  rw [integral_finsetSum _ (fun c _ => (prod_int h.ball (cont_Tc M lam β hβ K A (c + 1))).const_mul _),
    integral_finsetSum _ (fun c _ => (hd1 (c + 1)).const_mul _), Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [integral_const_mul, integral_const_mul, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg _) ?_)
  · exact term_bound h (fun w x => Gc M lam β K A (c + 1) w x)
      (fun w => cont_Gc M lam β hβ K A (c + 1) w) (c + 1) (by omega)
  · rw [pow_mul]; positivity

end chaos

/-! ## Decorrelation on the image measure -/

theorem decor_nu [Inhabited (Fin n)] (M : Mod n I J S G) (hT : TwoPt n J)
    {ν : Measure (Fin n → ℝ)} {Lam τ : ℝ} (h : SliceH M ν Lam τ)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    ∫ W : J × Fin n → ℝ,
        ((∫ x, Fm M P lam W x ∂ν) -
          ∫ W' : J × Fin n → ℝ, (∫ x, Fm M P lam W' x ∂ν) ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) ≤
      Lam * ∫ x, (∫ W : J × Fin n → ℝ,
          (Fm M P lam W x - ∫ W' : J × Fin n → ℝ, Fm M P lam W' x ∂stdGauss (J × Fin n)) ^ 2
          ∂stdGauss (J × Fin n)) ∂ν := by
  have hprob := h.prob
  have hν := h.ball
  obtain ⟨ι, _, β, Q, hβ, hrep⟩ := rep_poly M P
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k, (Q k).totalDegree ≤ K :=
    ⟨Finset.univ.sup fun k => (Q k).totalDegree, fun k =>
      Finset.le_sup (f := fun k => (Q k).totalDegree) (Finset.mem_univ k)⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ι → Tens n, ∀ k, A k = tensOf K (cOf K (Q k)) := ⟨_, fun _ => rfl⟩
  have hA : ∀ k j, IsSymmT (A k j) := fun k => by
    rw [hAdef]; exact BstLean.Part59.tensOf_symm59x n K (cOf K (Q k))
  have hval : ∀ k (y : Fin n → ℝ), fvA K (A k) y = MvPolynomial.eval y (Q k) := by
    intro k y
    rw [hAdef, BstLean.Part59.fvA_tensOf59x, polyEval_cOf K (Q k) (hK k)]
  have hF : ∀ (W : J × Fin n → ℝ) (x : Fin n → ℝ),
      Fm M P lam W x = ∑ k, β k x * fvA K (A k) (fun i => lam * zv W (M.ps x) i) := by
    intro W x
    unfold Fm
    rw [hrep]
    exact Finset.sum_congr rfl fun k _ => by rw [hval]
  obtain ⟨-, gF, gB, hswap, htwoswap⟩ := sep_facts hν (sep_Fm M P lam)
  -- the mean
  have hm : ∀ x, ∫ W : J × Fin n → ℝ, Fm M P lam W x ∂stdGauss (J × Fin n) =
      Gc M lam β K A 0 (fun i => i.elim0) x := by
    intro x
    simp_rw [hF]
    rw [integral_finsetSum _ fun k _ => ((onePt hT K (A k) (hA k) lam (M.ps x)).1).const_mul _]
    unfold Gc
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (onePt hT K (A k) (hA k) lam (M.ps x)).2, kap_diag]
  -- the two-point function
  have h2 : ∀ x y, ∫ W : J × Fin n → ℝ, Fm M P lam W x * Fm M P lam W y ∂stdGauss (J × Fin n) =
      Gc M lam β K A 0 (fun i => i.elim0) x * Gc M lam β K A 0 (fun i => i.elim0) y +
        Rr M lam β K A x y := by
    intro x y
    have e : ∀ W : J × Fin n → ℝ, Fm M P lam W x * Fm M P lam W y =
        ∑ k, ∑ l, β k x * β l y * (fvA K (A k) (fun i => lam * zv W (M.ps x) i) *
          fvA K (A l) (fun i => lam * zv W (M.ps y) i)) := by
      intro W
      rw [hF, hF, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e]
    have hint : ∀ k l, Integrable (fun W : J × Fin n → ℝ =>
        β k x * β l y * (fvA K (A k) (fun i => lam * zv W (M.ps x) i) *
          fvA K (A l) (fun i => lam * zv W (M.ps y) i))) (stdGauss (J × Fin n)) :=
      fun k l => ((hT K (A k) (A l) (hA k) (hA l) lam (M.ps x) (M.ps y)).1).const_mul _
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
    simp_rw [integral_finsetSum _ fun l _ => hint _ l, integral_const_mul,
      (hT K (A _) (A _) (hA _) (hA _) lam (M.ps x) (M.ps y)).2, ← kap_diag]
    have e3 : ∀ k l : ι, β k x * β l y *
        ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lam ^ (2 * c) *
          tinner (heatA K (lam ^ 2 * kapm M x x) (A k) c)
            (heatA K (lam ^ 2 * kapm M y y) (A l) c) * (∑ q, M.ps x q * M.ps y q) ^ c =
        ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lam ^ (2 * c) * (β k x * β l y *
          tinner (heatA K (lam ^ 2 * kapm M x x) (A k) c)
            (heatA K (lam ^ 2 * kapm M y y) (A l) c)) * kapm M x y ^ c := by
      intro k l
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by unfold kapm; ring
    simp_rw [e3]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := Finset.range (K + 1))]
    have e4 : ∀ c : ℕ, ∑ k, ∑ l, (c.factorial : ℝ) * lam ^ (2 * c) * (β k x * β l y *
          tinner (heatA K (lam ^ 2 * kapm M x x) (A k) c)
            (heatA K (lam ^ 2 * kapm M y y) (A l) c)) * kapm M x y ^ c =
        (c.factorial : ℝ) * lam ^ (2 * c) * Tc M lam β K A c x y := by
      intro c
      unfold Tc
      rw [gc_tinner, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl fun c _ => (Finset.sum_comm.trans (e4 c))]
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    unfold Tc
    have hu : ∀ w : Fin 0 → Fin n, w = fun i => i.elim0 := fun w => Subsingleton.elim _ _
    rw [Fintype.sum_eq_single (fun i : Fin 0 => i.elim0) (fun w hw => absurd (hu w) hw)]
    simp
  have hmc : Continuous (Gc M lam β K A 0 (fun i => i.elim0)) := cont_Gc M lam β hβ K A 0 _
  have hRc : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Rr M lam β K A z.1 z.2) := by
    unfold Rr
    exact continuous_finsetSum _ fun c _ => continuous_const.mul (cont_Tc M lam β hβ K A (c + 1))
  have hμ : ∫ W : J × Fin n → ℝ, (∫ x, Fm M P lam W x ∂ν) ∂stdGauss (J × Fin n) =
      ∫ x, Gc M lam β K A 0 (fun i => i.elim0) x ∂ν :=
    hswap.trans (integral_congr_ae (ae_of_all _ hm))
  have hB2 : ∫ W : J × Fin n → ℝ, (∫ x, Fm M P lam W x ∂ν) ^ 2 ∂stdGauss (J × Fin n) =
      (∫ x, Gc M lam β K A 0 (fun i => i.elim0) x ∂ν) ^ 2 +
        ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Rr M lam β K A z.1 z.2 ∂(ν.prod ν) := by
    have h' : ∫ W : J × Fin n → ℝ, (∫ x, Fm M P lam W x ∂ν) ^ 2 ∂stdGauss (J × Fin n) =
        ∫ x, ∫ y, (Gc M lam β K A 0 (fun i => i.elim0) x * Gc M lam β K A 0 (fun i => i.elim0) y +
          Rr M lam β K A x y) ∂ν ∂ν := by
      refine htwoswap.trans ?_
      simp_rw [h2]
    exact h'.trans (prod_split hν hmc hRc)
  obtain ⟨μB, hμB⟩ : ∃ μB : ℝ,
      μB = ∫ W : J × Fin n → ℝ, (∫ x, Fm M P lam W x ∂ν) ∂stdGauss (J × Fin n) := ⟨_, rfl⟩
  rw [← hμB]
  have hL : ∫ W : J × Fin n → ℝ, ((∫ x, Fm M P lam W x ∂ν) - μB) ^ 2 ∂stdGauss (J × Fin n) =
      ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Rr M lam β K A z.1 z.2 ∂(ν.prod ν) := by
    have gB2 : Integrable (fun W : J × Fin n → ℝ =>
        (∫ x, Fm M P lam W x ∂ν) * (∫ x, Fm M P lam W x ∂ν)) (stdGauss (J × Fin n)) :=
      (gB.mul gB).integrable
    rw [var_expand (stdGauss (J × Fin n)) gB.integrable gB2 μB, ← hμB]
    simp_rw [← sq]
    rw [hB2, ← hμ, ← hμB]
    ring
  have hRx : ∀ x : Fin n → ℝ, ∫ W : J × Fin n → ℝ,
      (Fm M P lam W x - ∫ W' : J × Fin n → ℝ, Fm M P lam W' x ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) = Rr M lam β K A x x := by
    intro x
    rw [hm x]
    obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = Gc M lam β K A 0 (fun i => i.elim0) x := ⟨_, rfl⟩
    rw [← hmx]
    rw [var_expand (stdGauss (J × Fin n)) (gF x).integrable ((gF x).mul (gF x)).integrable mx,
      h2 x x, hm x, ← hmx]
    ring
  rw [hL]
  simp_rw [hRx]
  exact rr_bound h lam β hβ K A

end Dec

open Dec in
/-- **Slice decorrelation.** -/
theorem decor86 {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    [MeasurableSpace G] (M : Mod n I J S G) (d : ℕ) (Lam : ℝ) (hR : Reg M d) (hT : TwoPt n J)
    (hS : SliceOp M Lam) (hL : 0 ≤ Lam) : Decor86 M Lam := by
  intro P lam p
  obtain ⟨-, hga, hX, hball, -, -⟩ := hR
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hc : ∀ W W' : J × Fin 0 → ℝ, msl M P lam W p = msl M P lam W' p := by
      intro W W'
      unfold msl Fs Fm
      have : ∀ x : Fin 0 → ℝ, (fun i : Fin 0 => lam * zv W (M.ps x) i) =
          fun i => lam * zv W' (M.ps x) i := fun x => funext fun i => i.elim0
      simp_rw [this]
    have h0 : ∀ W : J × Fin 0 → ℝ,
        (msl M P lam W p - ∫ W' : J × Fin 0 → ℝ, msl M P lam W' p ∂stdGauss (J × Fin 0)) ^ 2 =
          0 := by
      intro W
      have : (fun W' : J × Fin 0 → ℝ => msl M P lam W' p) = fun _ => msl M P lam W p :=
        funext fun W' => hc W' W
      rw [this, integral_const]
      simp
    simp_rw [h0]
    rw [integral_zero]
    exact mul_nonneg hL (integral_nonneg fun g => integral_nonneg fun W => sq_nonneg _)
  have : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨τ, hτ0, hτ, hop⟩ := hS p
  have hmeas : Measurable (fun g : G => M.X (p, g)) := hX.comp measurable_prodMk_left
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure (Fin n → ℝ), ν = M.ga.map (fun g : G => M.X (p, g)) :=
    ⟨_, rfl⟩
  have hmap : ∀ f : (Fin n → ℝ) → ℝ, Continuous f →
      ∫ x, f x ∂ν = ∫ g, f (M.X (p, g)) ∂M.ga := fun f hf => by
    rw [hνdef]; exact integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  have hH : SliceH M ν Lam τ := by
    refine ⟨?_, ?_, hL, hτ0, ?_, ?_⟩
    · rw [hνdef]; exact (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 hga
    · rw [hνdef]
      have hs : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ^ 2 ≤ 1} :=
        measurableSet_le (by fun_prop) measurable_const
      exact (ae_map_iff hmeas.aemeasurable hs).2 (ae_of_all _ fun g => hball (p, g))
    · rw [hνdef]
      have hs : MeasurableSet {x : Fin n → ℝ | τ ≤ kapm M x x} :=
        measurableSet_le measurable_const (cont_kap_diag M).measurable
      exact (ae_map_iff hmeas.aemeasurable hs).2 hτ
    · intro c
      have hc' : Continuous (fun x : Fin n → ℝ => (∑ q, c q * M.ps x q) ^ 2) :=
        (continuous_finsetSum _ fun q _ => continuous_const.mul (cont_ps M q)).pow 2
      rw [hmap _ hc']
      exact hop c
  have hprob := hH.prob
  obtain ⟨hFc, gF, -, -, -⟩ := sep_facts hH.ball (sep_Fm M P lam)
  have hmsl : ∀ W : J × Fin n → ℝ, msl M P lam W p = ∫ x, Fm M P lam W x ∂ν := fun W =>
    (hmap _ (hFc W)).symm
  have key := decor_nu M hT hH P lam
  simp_rw [hmsl]
  refine key.trans (le_of_eq ?_)
  congr 1
  -- the inner variance is a continuous function of `x`
  obtain ⟨V, hV⟩ : ∃ V : (Fin n → ℝ) → ℝ, ∀ x, V x = ∫ W : J × Fin n → ℝ,
      (Fm M P lam W x - ∫ W' : J × Fin n → ℝ, Fm M P lam W' x ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) := ⟨_, fun _ => rfl⟩
  have hVm : Measurable V := by
    obtain ⟨ι, _, g, h, hg, hh, e⟩ := sep_Fm M P lam
    have e1 : ∀ x, ∫ W' : J × Fin n → ℝ, Fm M P lam W' x ∂stdGauss (J × Fin n) =
        ∑ k, (∫ W, g k W ∂stdGauss (J × Fin n)) * h k x := by
      intro x
      simp_rw [e]
      rw [integral_finsetSum _ fun k _ => ((hg k).integrable).mul_const _]
      simp_rw [integral_mul_const]
    have e2 : ∀ x, V x = ∑ kl : ι × ι,
        (∫ W, (g kl.1 W - ∫ W', g kl.1 W' ∂stdGauss (J × Fin n)) *
          (g kl.2 W - ∫ W', g kl.2 W' ∂stdGauss (J × Fin n)) ∂stdGauss (J × Fin n)) *
          (h kl.1 x * h kl.2 x) := by
      intro x
      rw [hV]
      have e3 : ∀ W : J × Fin n → ℝ,
          (Fm M P lam W x - ∫ W' : J × Fin n → ℝ, Fm M P lam W' x ∂stdGauss (J × Fin n)) ^ 2 =
          ∑ kl : ι × ι, ((g kl.1 W - ∫ W', g kl.1 W' ∂stdGauss (J × Fin n)) *
            (g kl.2 W - ∫ W', g kl.2 W' ∂stdGauss (J × Fin n))) * (h kl.1 x * h kl.2 x) := by
        intro W
        rw [e1, e, ← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      simp_rw [e3]
      rw [integral_finsetSum _ fun kl _ =>
        ((((hg kl.1).sub (Good.const _)).mul ((hg kl.2).sub (Good.const _))).integrable).mul_const _]
      simp_rw [integral_mul_const]
    have : V = fun x => ∑ kl : ι × ι,
        (∫ W, (g kl.1 W - ∫ W', g kl.1 W' ∂stdGauss (J × Fin n)) *
          (g kl.2 W - ∫ W', g kl.2 W' ∂stdGauss (J × Fin n)) ∂stdGauss (J × Fin n)) *
          (h kl.1 x * h kl.2 x) := funext e2
    rw [this]
    exact (continuous_finsetSum _ fun kl _ =>
      continuous_const.mul ((hh kl.1).mul (hh kl.2))).measurable
  simp_rw [← hV]
  rw [hνdef, integral_map hmeas.aemeasurable hVm.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  show V (M.X (p, g)) = _
  rw [hV]
  rfl

end BstLean.Part86

#print axioms BstLean.Part86.decor86
