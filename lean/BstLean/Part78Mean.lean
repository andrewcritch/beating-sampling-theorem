import BstLean.Part78MeanA

/-!
# Part 78: `regIface` and `meanIds`

`FG a H W x = Σ_k cc H k (a, W) * psi k x`, a finite separable sum over `KK n = JJ n ⊕ JJ n × JJ n`.
All integrals over the sphere and over the Gaussian are computed term by term.
-/

namespace BstLean.Part78

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (Mono phiM varU)

variable {n : ℕ}

/-! ## The sphere -/

lemma sph_int (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

lemma cont_pf (q : JJ n) : Continuous (fun x : Fin n → ℝ => pf x q) := by
  unfold pf
  exact continuous_multiset_prod q.1.2.1 (fun i _ => continuous_apply i)

/-! ## The separable form of `FG` -/

/-- Index of the terms of `FG`. -/
abbrev KK (n : ℕ) := JJ n ⊕ (JJ n × JJ n)

/-- Coefficients (polynomials in `(a, W)`). -/
noncomputable def cc (H : Matrix (Fin n) (Fin n) ℝ) (k : KK n)
    (p : (Fin n → ℝ) × (WIdx n → ℝ)) : ℝ :=
  Sum.elim (fun q => ∑ i, p.1 i * p.2 (q, i))
    (fun qq => ∑ i, ∑ j, H i j * p.2 (qq.1, i) * p.2 (qq.2, j)) k

/-- Features (continuous functions of `x`). -/
noncomputable def psi (k : KK n) (x : Fin n → ℝ) : ℝ :=
  Sum.elim (fun q => pf x q) (fun qq => pf x qq.1 * pf x qq.2) k

lemma sum4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma FG_eq (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) (x : Fin n → ℝ) :
    FG a H W x = ∑ k, cc H k (a, W) * psi k x := by
  unfold FG Phi
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [cc, psi, Sum.elim_inl, Sum.elim_inr, zv]
  congr 1
  · simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
  · have h : ∀ i j : Fin n, H i j * (∑ q, W (q, i) * pf x q) * (∑ q, W (q, j) * pf x q) =
        ∑ q : JJ n, ∑ q' : JJ n, H i j * W (q, i) * W (q', j) * (pf x q * pf x q') := by
      intro i j
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q' _ => by ring
    simp_rw [h, Finset.sum_mul]
    exact sum4 _

lemma cont_psi (k : KK n) : Continuous (psi k) := by
  rcases k with q | qq
  · exact cont_pf q
  · exact (cont_pf qq.1).mul (cont_pf qq.2)

lemma cont_cc (H : Matrix (Fin n) (Fin n) ℝ) (k : KK n) : Continuous (cc H k) := by
  rcases k with q | qq
  · have : cc H (Sum.inl q) = fun p => ∑ i, p.1 i * p.2 (q, i) := rfl
    rw [this]; fun_prop
  · have : cc H (Sum.inr qq) = fun p => ∑ i, ∑ j, H i j * p.2 (qq.1, i) * p.2 (qq.2, j) := rfl
    rw [this]; fun_prop

lemma good_cc (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (k : KK n) :
    Good (stdGauss (WIdx n)) (fun W => cc H k (a, W)) := by
  rcases k with q | qq
  · simp only [cc, Sum.elim_inl]
    exact Good.sum _ fun i _ => (good_coord (q, i)).const_mul (a i)
  · simp only [cc, Sum.elim_inr]
    exact Good.sum _ fun i _ => Good.sum _ fun j _ =>
      ((good_coord (qq.1, i)).const_mul (H i j)).mul (good_coord (qq.2, j))

lemma int_psi (hn : 1 ≤ n) (k : KK n) : Integrable (psi k) (uniformSphere n) :=
  sph_int hn (cont_psi k)

lemma int_psi2 (hn : 1 ≤ n) (k l : KK n) :
    Integrable (fun x => psi k x * psi l x) (uniformSphere n) :=
  sph_int hn ((cont_psi k).mul (cont_psi l))

lemma cont_FG (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    Continuous (FG a H W) := by
  have : FG a H W = fun x => ∑ k, cc H k (a, W) * psi k x := funext (FG_eq a H W)
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (cont_psi k)

lemma intF_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    ∫ x, FG a H W x ∂uniformSphere n =
      ∑ k, cc H k (a, W) * ∫ x, psi k x ∂uniformSphere n := by
  simp_rw [FG_eq]
  exact sep_int (fun k (p : (Fin n → ℝ) × (WIdx n → ℝ)) => cc H k p) psi (int_psi hn) (a, W)

lemma intF2_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    ∫ x, FG a H W x ^ 2 ∂uniformSphere n =
      ∑ kl : KK n × KK n, (cc H kl.1 (a, W) * cc H kl.2 (a, W)) *
        ∫ x, psi kl.1 x * psi kl.2 x ∂uniformSphere n := by
  simp_rw [FG_eq]
  exact sep_int_sq (fun k (p : (Fin n → ℝ) × (WIdx n → ℝ)) => cc H k p) psi (int_psi2 hn) (a, W)

lemma VG_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    VG a H W = ∫ x, FG a H W x ^ 2 ∂uniformSphere n - (∫ x, FG a H W x ∂uniformSphere n) ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold VG varU
  set m := ∫ y, FG a H W y ∂uniformSphere n with hm
  have h1 : Integrable (FG a H W) (uniformSphere n) := sph_int hn (cont_FG a H W)
  have h2 : Integrable (fun x => FG a H W x ^ 2) (uniformSphere n) :=
    sph_int hn ((cont_FG a H W).pow 2)
  have h : ∀ x, (FG a H W x - m) ^ 2 = FG a H W x ^ 2 - 2 * m * FG a H W x + m ^ 2 := by
    intro x; ring
  simp_rw [h]
  have e1 := integral_add (h2.sub (h1.const_mul (2 * m))) (integrable_const (μ := uniformSphere n) (m ^ 2))
  have e2 := integral_sub h2 (h1.const_mul (2 * m))
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, ← hm]
  ring

/-- **Regularity.** -/
theorem regIface (n : ℕ) (hn : 1 ≤ n) : RegIface n := by
  intro H
  have hA : Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) =>
      ∫ x, FG p.1 H p.2 x ∂uniformSphere n) := by
    simp_rw [intF_eq hn]
    exact continuous_finsetSum _ fun k _ => (cont_cc H k).mul continuous_const
  have hB : Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) =>
      ∫ x, FG p.1 H p.2 x ^ 2 ∂uniformSphere n) := by
    simp_rw [intF2_eq hn]
    exact continuous_finsetSum _ fun kl _ =>
      ((cont_cc H kl.1).mul (cont_cc H kl.2)).mul continuous_const
  constructor
  · simp_rw [VG_eq hn]
    exact hB.sub (hA.pow 2)
  · unfold errG
    exact hA.sub continuous_const

/-! ## The kernel on the sphere -/

lemma cont_kap_diag : Continuous (fun x : Fin n → ℝ => kap x x) :=
  continuous_finsetSum _ fun q _ => (cont_pf q).mul (cont_pf q)

lemma cont_kap_right (x : Fin n → ℝ) : Continuous (fun y : Fin n → ℝ => kap x y) :=
  continuous_finsetSum _ fun q _ => continuous_const.mul (cont_pf q)

lemma cont_kap_int (hn : 1 ≤ n) :
    Continuous (fun x : Fin n → ℝ => ∫ y, kap x y ∂uniformSphere n) := by
  have h : ∀ x : Fin n → ℝ, ∫ y, kap x y ∂uniformSphere n =
      ∑ q : JJ n, pf x q * ∫ y, pf y q ∂uniformSphere n := fun x =>
    sep_int (fun (q : JJ n) (x : Fin n → ℝ) => pf x q) (fun (q : JJ n) (y : Fin n → ℝ) => pf y q)
      (fun q => sph_int hn (cont_pf q)) x
  simp_rw [h]
  exact continuous_finsetSum _ fun q _ => (cont_pf q).mul continuous_const

lemma cont_kap_int2 (hn : 1 ≤ n) :
    Continuous (fun x : Fin n → ℝ => ∫ y, kap x y ^ 2 ∂uniformSphere n) := by
  have h : ∀ x : Fin n → ℝ, ∫ y, kap x y ^ 2 ∂uniformSphere n =
      ∑ kl : JJ n × JJ n, (pf x kl.1 * pf x kl.2) *
        ∫ y, pf y kl.1 * pf y kl.2 ∂uniformSphere n := fun x =>
    sep_int_sq (fun (q : JJ n) (x : Fin n → ℝ) => pf x q) (fun (q : JJ n) (y : Fin n → ℝ) => pf y q)
      (fun q q' => sph_int hn ((cont_pf q).mul (cont_pf q'))) x
  simp_rw [h]
  exact continuous_finsetSum _ fun kl _ =>
    ((cont_pf kl.1).mul (cont_pf kl.2)).mul continuous_const

/-- `E_x R(x,x)`. -/
lemma sph_diag (hn : 1 ≤ n) (A T Fr : ℝ) :
    ∫ x, (A * kap x x + T * (kap x x * kap x x) + Fr * kap x x ^ 2) ∂uniformSphere n =
      A * tG n + T * kk2 n + Fr * kk2 n := by
  have h1 : Integrable (fun x : Fin n → ℝ => kap x x) (uniformSphere n) := sph_int hn cont_kap_diag
  have h2 : Integrable (fun x : Fin n → ℝ => kap x x ^ 2) (uniformSphere n) :=
    sph_int hn (cont_kap_diag.pow 2)
  have h : ∀ x : Fin n → ℝ, A * kap x x + T * (kap x x * kap x x) + Fr * kap x x ^ 2 =
      A * kap x x + (T * kap x x ^ 2 + Fr * kap x x ^ 2) := by intro x; ring
  simp_rw [h]
  have e1 := integral_add (h1.const_mul A) ((h2.const_mul T).add (h2.const_mul Fr))
  have e2 := integral_add (h2.const_mul T) (h2.const_mul Fr)
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  unfold tG kk2
  ring

/-- `E_{x,y} R(x,y)`. -/
lemma sph_off (hn : 1 ≤ n) (A T Fr : ℝ) :
    ∫ x, ∫ y, (A * kap x y + T * (kap x x * kap y y) + Fr * kap x y ^ 2)
        ∂uniformSphere n ∂uniformSphere n =
      A * mm1 n + T * tG n ^ 2 + Fr * ss2 n := by
  have h1 : Integrable (fun x : Fin n → ℝ => kap x x) (uniformSphere n) := sph_int hn cont_kap_diag
  have hin : ∀ x : Fin n → ℝ,
      ∫ y, (A * kap x y + T * (kap x x * kap y y) + Fr * kap x y ^ 2) ∂uniformSphere n =
        A * (∫ y, kap x y ∂uniformSphere n) + ((T * tG n) * kap x x +
          Fr * ∫ y, kap x y ^ 2 ∂uniformSphere n) := by
    intro x
    have i1 : Integrable (fun y : Fin n → ℝ => kap x y) (uniformSphere n) :=
      sph_int hn (cont_kap_right x)
    have i2 : Integrable (fun y : Fin n → ℝ => kap x y ^ 2) (uniformSphere n) :=
      sph_int hn ((cont_kap_right x).pow 2)
    have h : ∀ y : Fin n → ℝ, A * kap x y + T * (kap x x * kap y y) + Fr * kap x y ^ 2 =
        A * kap x y + ((T * kap x x) * kap y y + Fr * kap x y ^ 2) := by intro y; ring
    simp_rw [h]
    have e1 := integral_add (i1.const_mul A) ((h1.const_mul (T * kap x x)).add (i2.const_mul Fr))
    have e2 := integral_add (h1.const_mul (T * kap x x)) (i2.const_mul Fr)
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
    unfold tG
    ring
  simp_rw [hin]
  have j1 : Integrable (fun x : Fin n → ℝ => ∫ y, kap x y ∂uniformSphere n) (uniformSphere n) :=
    sph_int hn (cont_kap_int hn)
  have j2 : Integrable (fun x : Fin n → ℝ => ∫ y, kap x y ^ 2 ∂uniformSphere n)
      (uniformSphere n) := sph_int hn (cont_kap_int2 hn)
  have e1 := integral_add (j1.const_mul A) ((h1.const_mul (T * tG n)).add (j2.const_mul Fr))
  have e2 := integral_add (h1.const_mul (T * tG n)) (j2.const_mul Fr)
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  unfold mm1 ss2 tG
  ring

/-! ## The Gaussian side -/

lemma wick1 (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (x : Fin n → ℝ) :
    ∫ W, FG a H W x ∂stdGauss (WIdx n) = trH H * kap x x := by
  have h := (hW (JJ n) n a H hH (pf x) (pf x)).1
  have hk : kap x x = ∑ q : JJ n, pf x q ^ 2 := by
    unfold kap; exact Finset.sum_congr rfl fun q _ => by ring
  rw [hk]
  exact h

lemma wick2 (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (x y : Fin n → ℝ) :
    ∫ W, FG a H W x * FG a H W y ∂stdGauss (WIdx n) =
      nsq a * kap x y + trH H ^ 2 * (kap x x * kap y y) + 2 * frobH H * kap x y ^ 2 := by
  have h := (hW (JJ n) n a H hH (pf x) (pf y)).2
  have hk : ∀ z : Fin n → ℝ, kap z z = ∑ q : JJ n, pf z q ^ 2 := by
    intro z; unfold kap; exact Finset.sum_congr rfl fun q _ => by ring
  rw [hk x, hk y]
  exact h

/-- **The exact conditional identities.** -/
theorem meanIds (n : ℕ) (hn : 1 ≤ n) (hW : WickTwoPoint) : MeanIds n := by
  intro a H hH
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  -- the two sphere integrals of `FG`, as functions of `W`
  have gA : Good (stdGauss (WIdx n)) (fun W => ∫ x, FG a H W x ∂uniformSphere n) := by
    simp_rw [intF_eq hn]
    exact Good.sum _ fun k _ => (good_cc a H k).mul_const _
  have gB : Good (stdGauss (WIdx n)) (fun W => ∫ x, FG a H W x ^ 2 ∂uniformSphere n) := by
    simp_rw [intF2_eq hn]
    exact Good.sum _ fun kl _ => ((good_cc a H kl.1).mul (good_cc a H kl.2)).mul_const _
  have gV : Good (stdGauss (WIdx n)) (VG a H) := by
    have : VG a H = fun W => ∫ x, FG a H W x ^ 2 ∂uniformSphere n -
        (∫ x, FG a H W x ∂uniformSphere n) ^ 2 := funext (VG_eq hn a H)
    rw [this]
    exact gB.sub (gA.pow 2)
  have gE : Good (stdGauss (WIdx n)) (errG a H) := by
    have : errG a H = fun W => ∫ x, FG a H W x ∂uniformSphere n - 3 / 2 * trH H := rfl
    rw [this]
    exact gA.sub (Good.const _)
  have hc1 : ∀ k, Integrable (fun W => cc H k (a, W)) (stdGauss (WIdx n)) := fun k => (good_cc a H k).integrable
  have hc2 : ∀ k l, Integrable (fun W => cc H k (a, W) * cc H l (a, W)) (stdGauss (WIdx n)) :=
    fun k l => ((good_cc a H k).mul (good_cc a H l)).integrable
  -- exchanges of the integrals
  have E1 : ∫ W, ∫ x, FG a H W x ∂uniformSphere n ∂stdGauss (WIdx n) = trH H * tG n := by
    have h : ∫ W, ∫ x, FG a H W x ∂uniformSphere n ∂stdGauss (WIdx n) =
        ∫ x, ∫ W, FG a H W x ∂stdGauss (WIdx n) ∂uniformSphere n := by
      simp_rw [FG_eq]
      exact sep_swap (μ := (stdGauss (WIdx n))) (ν := uniformSphere n) (fun k W => cc H k (a, W)) psi hc1
        (int_psi hn)
    rw [h]
    simp_rw [wick1 hW a H hH]
    rw [integral_const_mul]
    rfl
  have E2 : ∫ W, ∫ x, FG a H W x ^ 2 ∂uniformSphere n ∂stdGauss (WIdx n) =
      nsq a * tG n + trH H ^ 2 * kk2 n + 2 * frobH H * kk2 n := by
    have h : ∫ W, ∫ x, FG a H W x ^ 2 ∂uniformSphere n ∂stdGauss (WIdx n) =
        ∫ x, ∫ W, FG a H W x ^ 2 ∂stdGauss (WIdx n) ∂uniformSphere n := by
      simp_rw [FG_eq]
      exact sep_swap_sq (μ := (stdGauss (WIdx n))) (ν := uniformSphere n) (fun k W => cc H k (a, W)) psi hc2
        (int_psi2 hn)
    rw [h]
    simp_rw [sq (FG a H _ _), wick2 hW a H hH]
    exact sph_diag hn _ _ _
  have E3 : ∫ W, (∫ x, FG a H W x ∂uniformSphere n) ^ 2 ∂stdGauss (WIdx n) =
      nsq a * mm1 n + trH H ^ 2 * tG n ^ 2 + 2 * frobH H * ss2 n := by
    have h : ∫ W, (∫ x, FG a H W x ∂uniformSphere n) ^ 2 ∂stdGauss (WIdx n) =
        ∫ x, ∫ y, ∫ W, FG a H W x * FG a H W y ∂stdGauss (WIdx n) ∂uniformSphere n ∂uniformSphere n := by
      simp_rw [FG_eq]
      exact sep_swap_two (μ := (stdGauss (WIdx n))) (ν := uniformSphere n) (fun k W => cc H k (a, W)) psi hc2
        (int_psi hn)
    rw [h]
    simp_rw [wick2 hW a H hH]
    exact sph_off hn _ _ _
  refine ⟨gV.integrable, (gV.pow 2).integrable, (gE.pow 2).integrable, ?_, ?_⟩
  · simp_rw [VG_eq hn]
    rw [integral_sub gB.integrable (gA.pow 2).integrable, E2, E3]
    ring
  · have h : ∀ W, errG a H W ^ 2 = (∫ x, FG a H W x ∂uniformSphere n) ^ 2 -
        (2 * (3 / 2 * trH H)) * (∫ x, FG a H W x ∂uniformSphere n) + (3 / 2 * trH H) ^ 2 := by
      intro W; unfold errG; ring
    simp_rw [h]
    have e1 := integral_add (((gA.pow 2).integrable).sub (gA.integrable.const_mul (2 * (3 / 2 * trH H))))
      (integrable_const (μ := (stdGauss (WIdx n))) ((3 / 2 * trH H) ^ 2))
    have e2 := integral_sub ((gA.pow 2).integrable) (gA.integrable.const_mul (2 * (3 / 2 * trH H)))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const, E1, E3]
    simp only [probReal_univ, smul_eq_mul]
    ring

end BstLean.Part78

#print axioms BstLean.Part78.regIface
#print axioms BstLean.Part78.meanIds
