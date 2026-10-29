import BstLean.Part84Defs
import BstLean.Part53Wick
import BstLean.Part59LemmaQ_Bridge
import BstLean.Part81Bridge

/-!
# Part 84, representation: every polynomial of degree `≤ K` has a representing symmetric family

`repIface : RepIface n d` (for `1 ≤ n`, `1 ≤ d`). The family is `tensOf K c` for the coefficient
vector `c` of `P`. The two-point identity is Part 53's Lemma W at `ψ = ψ₀(x)` (the features with the
constant one removed), moved from the full Gaussian coefficient vector to its non-constant part
by Part 81's split.
-/

namespace BstLean.Part84

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD monoVal)
open BstLean.Part41 (Mono phiM colM IsSymmT Tens contr trL)
open BstLean.Part53 (heatA tinner fvA linZ nsq wpair c0)
open BstLean.Part59 (polyEval tensOf)
open BstLean.Part78 (zv)
open BstLean.Part81 (JJ WIdx pf kap eD)

namespace Rep

variable {n d : ℕ}

/-! ## §1 The coefficient vector of a polynomial -/

/-- The coefficient vector of `P` on the monomials of degree `≤ K`. -/
noncomputable def cOf (K : ℕ) (P : MvPolynomial (Fin n) ℝ) : Mono n K → ℝ :=
  fun α => P.coeff (Multiset.toFinsupp α.2.1)

lemma polyEval_cOf (K : ℕ) (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ K)
    (y : Fin n → ℝ) : polyEval K (cOf K P) y = MvPolynomial.eval y P := by
  classical
  rw [MvPolynomial.eval_eq']
  unfold polyEval
  let e : Mono n K → (Fin n →₀ ℕ) := fun α => Multiset.toFinsupp α.2.1
  have he : Function.Injective e := by
    intro α β h
    have h1 : α.2.1 = β.2.1 := Multiset.toFinsupp.injective h
    obtain ⟨i, q⟩ := α
    obtain ⟨j, q'⟩ := β
    have hij : i = j := Fin.ext (by
      rw [← q.2, ← q'.2]
      exact congrArg Multiset.card h1)
    subst hij
    exact congrArg _ (Subtype.ext h1)
  have hterm : ∀ α : Mono n K,
      cOf K P α * phiM y α = P.coeff (e α) * ∏ i, y i ^ (e α) i := by
    intro α
    simp [cOf, phiM, BstLean.Part59.mono_powers59x, e, Multiset.toFinsupp_apply]
  simp_rw [hterm]
  rw [← Finset.sum_image (f := fun m => P.coeff m * ∏ i, y i ^ m i)
    (fun a _ b _ h => he h)]
  symm
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_image]
    have hdeg : (m.sum fun _ a => a) ≤ K := le_trans (MvPolynomial.le_totalDegree hm) hP
    refine ⟨⟨⟨Multiset.card (Finsupp.toMultiset m), ?_⟩, ⟨Finsupp.toMultiset m, rfl⟩⟩,
      Finset.mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset]; exact Nat.lt_succ_of_le hdeg
    · simp [e]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

/-! ## §2 The features without the constant one -/

/-- `ψ₀(x)`: the feature vector with the constant feature set to `0`. -/
noncomputable def psi0 (d : ℕ) (x : Fin n → ℝ) : Mono n d → ℝ :=
  fun p => if p = default then 0 else phiM x p

lemma sum_JJ (F : Mono n d → ℝ) :
    ∑ p : Mono n d, (if p = default then 0 else F p) = ∑ q : JJ n d, F q.1 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Mono n d => p ≠ default))
    (by simp) F, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p = default <;> simp [h]

lemma psi0_inner (x y : Fin n → ℝ) : ∑ p, psi0 d x p * psi0 d y p = kap d x y := by
  unfold kap pf
  rw [← sum_JJ (fun p => phiM x p * phiM y p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold psi0
  by_cases h : p = default <;> simp [h]

lemma psi0_nsq (x : Fin n → ℝ) : nsq (psi0 d x) = kap d x x := by
  rw [← psi0_inner]
  unfold nsq
  refine Finset.sum_congr rfl fun p _ => by ring

lemma linZ_comb (u : Fin n → ℝ) (W : WIdx n d → ℝ) (x : Fin n → ℝ) :
    linZ (BstLean.Part81.Br.combEquiv n d (u, W)) (psi0 d x) = zv W (pf x) := by
  funext a
  unfold linZ zv pf
  have h1 : ∀ p : Mono n d,
      colM (BstLean.Part81.Br.combEquiv n d (u, W)) p a * psi0 d x p =
        if p = default then 0
        else colM (BstLean.Part81.Br.combEquiv n d (u, W)) p a * phiM x p := by
    intro p
    unfold psi0
    by_cases h : p = default <;> simp [h]
  simp_rw [h1]
  rw [sum_JJ (fun p => colM (BstLean.Part81.Br.combEquiv n d (u, W)) p a * phiM x p)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have : colM (BstLean.Part81.Br.combEquiv n d (u, W)) q.1 a = W (q, a) :=
    BstLean.Part81.Br.combEquiv_inr u W q a
  rw [this]

/-! ## §3 From the full coefficient vector to its non-constant part -/

lemma transfer (H : (WIdx n d → ℝ) → ℝ) (G : (CoefIdxD n d → ℝ) → ℝ)
    (hGH : ∀ u W, G (BstLean.Part81.Br.combEquiv n d (u, W)) = H W) :
    (Integrable G (stdGauss (CoefIdxD n d)) → Integrable H (stdGauss (WIdx n d))) ∧
    ∫ Z, G Z ∂stdGauss (CoefIdxD n d) = ∫ W, H W ∂stdGauss (WIdx n d) := by
  have hmp := BstLean.Part81.Br.combEquiv_preserving (n := n) (d := d)
  have hfun : (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) =>
      G (BstLean.Part81.Br.combEquiv n d p)) = fun p => H p.2 := by
    funext p
    exact hGH p.1 p.2
  constructor
  · intro hG
    have h1 : Integrable (G ∘ BstLean.Part81.Br.combEquiv n d)
        ((stdGauss (Fin n)).prod (stdGauss (WIdx n d))) :=
      (hmp.integrable_comp_emb (BstLean.Part81.Br.combEquiv n d).measurableEmbedding).2 hG
    have h2 : Integrable (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => H p.2)
        ((stdGauss (Fin n)).prod (stdGauss (WIdx n d))) := by
      rw [← hfun]; exact h1
    obtain ⟨u, hu⟩ := h2.prod_right_ae.exists
    exact hu
  · rw [← hmp.integral_comp' G, hfun, integral_fun_snd]
    simp

/-! ## §4 The two-point identity on the non-constant part -/

lemma twoPoint (K : ℕ) (A B : Tens n) (hA : ∀ j, IsSymmT (A j)) (hB : ∀ j, IsSymmT (B j))
    (lam : ℝ) (x y : Fin n → ℝ) :
    Integrable (fun W : WIdx n d → ℝ =>
      fvA K A (lam • zv W (pf x)) * fvA K B (lam • zv W (pf y))) (stdGauss (WIdx n d)) ∧
    ∫ W : WIdx n d → ℝ, fvA K A (lam • zv W (pf x)) * fvA K B (lam • zv W (pf y))
        ∂stdGauss (WIdx n d) =
      ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lam ^ (2 * c) *
        tinner (heatA K (lam ^ 2 * kap d x x) A c) (heatA K (lam ^ 2 * kap d y y) B c) *
        kap d x y ^ c := by
  obtain ⟨hint, heq⟩ := BstLean.Part53.lemmaW53 K n d lam A B hA hB (psi0 d x) (psi0 d y)
  obtain ⟨t1, t2⟩ := transfer (n := n) (d := d)
    (fun W => fvA K A (lam • zv W (pf x)) * fvA K B (lam • zv W (pf y)))
    (fun Z => fvA K A (lam • linZ Z (psi0 d x)) * fvA K B (lam • linZ Z (psi0 d y)))
    (fun u W => by simp only [linZ_comb])
  refine ⟨t1 hint, ?_⟩
  rw [← t2, heq]
  unfold wpair
  rw [psi0_nsq, psi0_nsq, psi0_inner]

/-! ## §5 The family of the constant polynomial `1` -/

/-- The family of the constant polynomial `1`. -/
def unitT (n : ℕ) : Tens n := fun j _ => if j = 0 then 1 else 0

lemma unitT_symm (j : ℕ) : IsSymmT (unitT n j) := fun _ _ => rfl

lemma unitT_pos (j : ℕ) (hj : j ≠ 0) : unitT n j = fun _ => 0 := by
  funext w; simp [unitT, hj]

lemma fvA_unitT (K : ℕ) (y : Fin n → ℝ) : fvA K (unitT n) y = 1 := by
  unfold fvA
  rw [Finset.sum_eq_single 0]
  · simp [contr, unitT]
  · intro c _ hc
    simp [contr, unitT_pos c hc]
  · simp

lemma heat_unitT_pos (K : ℕ) (v : ℝ) (c : ℕ) (hc : c ≠ 0) :
    heatA K v (unitT n) c = fun _ => 0 := by
  funext w
  unfold heatA
  apply Finset.sum_eq_zero
  intro i _
  have : c + 2 * i ≠ 0 := by omega
  simp [trL, unitT_pos _ this]

lemma heat_unitT_zero (K : ℕ) (v : ℝ) (w : Fin 0 → Fin n) :
    heatA K v (unitT n) 0 w = 1 := by
  unfold heatA
  rw [Finset.sum_eq_single 0]
  · simp [trL, unitT]
  · intro i _ hi
    have : 0 + 2 * i ≠ 0 := by omega
    simp [trL, unitT_pos _ this]
  · simp

lemma tinner_zero_order (a b : (Fin 0 → Fin n) → ℝ) :
    tinner a b = a (fun i => i.elim0) * b (fun i => i.elim0) := by
  unfold tinner
  rw [Fintype.sum_eq_single (fun i : Fin 0 => (i.elim0 : Fin n))]
  intro w hw
  exact absurd (funext fun i => i.elim0) hw

lemma fvA_at_zero (K : ℕ) (B : Tens n) : fvA K B (fun _ => 0) = B 0 (fun i => i.elim0) := by
  unfold fvA
  rw [Finset.sum_eq_single 0]
  · unfold contr
    rw [Fintype.sum_eq_single (fun i : Fin 0 => (i.elim0 : Fin n))]
    · simp
    · intro w hw
      exact absurd (funext fun i => i.elim0) hw
  · intro c _ hc
    unfold contr
    apply Finset.sum_eq_zero
    intro w _
    have : NeZero c := ⟨hc⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin c)) rfl, mul_zero]
  · simp

lemma one_le_eD (d : ℕ) (hd : 1 ≤ d) : 1 ≤ eD d := by
  unfold eD c0
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j : ℕ => (1 : ℝ) / (j.factorial : ℝ))
    (Finset.range_mono (show 2 ≤ d + 1 by omega)) (fun j _ _ => by positivity)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  simp only [one_div]
  linarith

end Rep

open BstLean.Part84.Rep in
/-- **Representation**: every polynomial of degree `≤ K` has a representing symmetric family. -/
theorem repIface (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) : RepIface n d := by
  intro K P hP
  have : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
  set A : Tens n := tensOf K (cOf K P) with hAdef
  have hA : ∀ j, IsSymmT (A j) := BstLean.Part59.tensOf_symm59x n K (cOf K P)
  have hval : ∀ y : Fin n → ℝ, fvA K A y = MvPolynomial.eval y P := by
    intro y
    rw [hAdef, BstLean.Part59.fvA_tensOf59x, polyEval_cOf K P hP]
  have hFW : ∀ (lam : ℝ) (W : WIdx n d → ℝ) (x : Fin n → ℝ),
      FW P lam W x = fvA K A (lam • zv W (pf x)) := by
    intro lam W x
    rw [hval]
    rfl
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · -- the value of `g₀`
    have he : 0 < eD d := lt_of_lt_of_le one_pos (one_le_eD d hd)
    have hs : Real.sqrt (eD d) ≠ 0 := Real.sqrt_ne_zero'.mpr he
    have h := BstLean.Part59.heat_integral_square59x K (Real.sqrt (eD d)) hs A hA (fun _ => 0)
    rw [Real.sq_sqrt he.le, fvA_at_zero] at h
    unfold g0P hmean
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show _ = fvA K A (fun i => 0 + Real.sqrt (eD d) * g i)
    rw [hval]
    simp
  · intro lam x
    obtain ⟨hint, heq⟩ := twoPoint (d := d) K A (unitT n) hA unitT_symm lam x x
    simp only [fvA_unitT, mul_one] at hint heq
    simp only [hFW]
    refine ⟨hint, ?_⟩
    rw [heq, Finset.sum_eq_single 0]
    · rw [tinner_zero_order, heat_unitT_zero]
      simp [hmean]
    · intro c _ hc
      rw [heat_unitT_pos K _ c hc]
      simp [tinner]
    · simp
  · intro lam x y
    simp only [hFW]
    exact twoPoint (d := d) K A A hA hA lam x y

end BstLean.Part84
