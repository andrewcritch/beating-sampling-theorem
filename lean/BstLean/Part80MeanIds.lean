import BstLean.Part80Defs
import BstLean.Part78Mean
import BstLean.Part78Wick

/-!
# Part 80: `meanIdsA`, the exact conditional identities (E) and (V)

`FA W x = f(mu x) + a(x)·z + zᵀHz`, `z = zv W (ψ x)`, is a finite separable sum
`Σ_k ccA H k W * psA k x`. All integrals are computed term by term; the Gaussian two-point
function comes from `wickTwoPoint` and `gaussLin` (Part 78) by polarization.

Also: `sphLaw_cont_integrable` (continuous ⇒ integrable under a distribution on the sphere).
-/

namespace BstLean.Part80

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part78 (nsq frobH trH qfun aU zv Phi Good good_coord sep_int sep_mul sep_int_sq
  sep_swap sep_swap_sq sep_swap_two wickTwoPoint gaussLin)

/-! ## Distributions on the sphere -/

section sphere
variable {n : ℕ} {ν : Measure (Fin n → ℝ)}

lemma sphLaw_ae_Icc (hν : SphLaw n ν) :
    ∀ᵐ x ∂ν, x ∈ Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  filter_upwards [hν.sphere] with x hx
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

/-- A continuous function is integrable under a distribution on the sphere. -/
theorem sphLaw_cont_integrable (hν : SphLaw n ν) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f ν := by
  have := hν.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [sphLaw_ae_Icc hν] with x hx
  exact hC (Set.mem_image_of_mem _ hx)

/-- A continuous function of two points is integrable under the product distribution. -/
theorem sphLaw_cont_integrable_prod (hν : SphLaw n ν) {G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hG : Continuous G) : Integrable G (ν.prod ν) := by
  have := hν.prob
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).prod (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ))))).bddAbove_image hG.norm.continuousOn
  apply Integrable.of_bound hG.aestronglyMeasurable C
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae (sphLaw_ae_Icc hν)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae (sphLaw_ae_Icc hν)
  filter_upwards [h1, h2] with z hz1 hz2
  exact hC (Set.mem_image_of_mem _ ⟨hz1, hz2⟩)

/-- The partial integral of a continuous function of two points is integrable. -/
theorem sphLaw_cont_integrable_right (hν : SphLaw n ν) {G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hG : Continuous G) : Integrable (fun x => ∫ y, G (x, y) ∂ν) ν := by
  have := hν.prob
  exact (sphLaw_cont_integrable_prod hν hG).integral_prod_left

end sphere

/-! ## The Gaussian two-point function -/

section gauss
variable {n : ℕ} {J : Type} [Fintype J]

/-- The linear part `a·z`. -/
def Lf (a : Fin n → ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) : ℝ := ∑ i, a i * zv W p i

/-- The quadratic part `zᵀHz`. -/
def Qf (H : Matrix (Fin n) (Fin n) ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) : ℝ :=
  ∑ i, ∑ j, H i j * zv W p i * zv W p j

lemma Phi_split (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) :
    Phi a H W p = Lf a W p + Qf H W p := rfl

lemma zv_neg (W : J × Fin n → ℝ) (p : J → ℝ) (i : Fin n) :
    zv W (fun q => -p q) i = -zv W p i := by
  simp [zv, Finset.sum_neg_distrib]

lemma Lf_neg (a : Fin n → ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) :
    Lf a W (fun q => -p q) = -Lf a W p := by
  simp [Lf, zv_neg, Finset.sum_neg_distrib]

lemma Qf_neg (H : Matrix (Fin n) (Fin n) ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) :
    Qf H W (fun q => -p q) = Qf H W p := by
  simp [Qf, zv_neg]

lemma Lf_zero (W : J × Fin n → ℝ) (p : J → ℝ) : Lf (0 : Fin n → ℝ) W p = 0 := by
  simp [Lf]

lemma good_zv (p : J → ℝ) (i : Fin n) :
    Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => zv W p i) :=
  Good.sum _ fun q _ => (good_coord (q, i)).mul_const (p q)

lemma good_Lf (a : Fin n → ℝ) (p : J → ℝ) :
    Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => Lf a W p) :=
  Good.sum _ fun i _ => (good_zv p i).const_mul (a i)

lemma good_Qf (H : Matrix (Fin n) (Fin n) ℝ) (p : J → ℝ) :
    Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => Qf H W p) :=
  Good.sum _ fun i _ => Good.sum _ fun j _ => ((good_zv p i).const_mul (H i j)).mul (good_zv p j)

lemma Lf_eq (a : Fin n → ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) :
    Lf a W p = ∑ β : J × Fin n, (a β.2 * p β.1) * W β := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  unfold Lf zv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => by ring

/-- `E[L_a(p) L_b(p')] = (a·b)(p·p')`. -/
lemma int_LL (a b : Fin n → ℝ) (p p' : J → ℝ) :
    ∫ W, Lf a W p * Lf b W p' ∂stdGauss (J × Fin n) =
      (∑ i, a i * b i) * ∑ q, p q * p' q := by
  simp_rw [Lf_eq]
  rw [(gaussLin (J × Fin n) (fun β => a β.2 * p β.1) (fun β => b β.2 * p' β.1)).2]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring

/-- `E[Q(p)] = tr H ‖p‖²`. -/
lemma int_Phi (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (p : J → ℝ) :
    ∫ W, (Lf a W p + Qf H W p) ∂stdGauss (J × Fin n) = trH H * ∑ q, p q ^ 2 :=
  (wickTwoPoint J n a H hH p p).1

/-- `E[L_a(p) Q(p')] = 0`. -/
lemma int_LQ (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (p p' : J → ℝ) :
    ∫ W, Lf a W p * Qf H W p' ∂stdGauss (J × Fin n) = 0 := by
  have w1 : ∫ W, (Lf a W p + Qf H W p) * (Lf a W p' + Qf H W p') ∂stdGauss (J × Fin n) =
      nsq a * (∑ q, p q * p' q) + trH H ^ 2 * ((∑ q, p q ^ 2) * (∑ q, p' q ^ 2)) +
        2 * frobH H * (∑ q, p q * p' q) ^ 2 := (wickTwoPoint J n a H hH p p').2
  have w2 : ∫ W, (-Lf a W p + Qf H W p) * (Lf a W p' + Qf H W p') ∂stdGauss (J × Fin n) =
      -(nsq a * (∑ q, p q * p' q)) + trH H ^ 2 * ((∑ q, p q ^ 2) * (∑ q, p' q ^ 2)) +
        2 * frobH H * (∑ q, p q * p' q) ^ 2 := by
    have h := (wickTwoPoint J n a H hH (fun q => -p q) p').2
    simp only [Phi_split, Lf_neg, Qf_neg] at h
    rw [h]
    have e1 : ∑ q, -p q * p' q = -∑ q, p q * p' q := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
    have e2 : ∑ q, (-p q) ^ 2 = ∑ q, p q ^ 2 := Finset.sum_congr rfl fun q _ => by ring
    rw [e1, e2]; ring
  have gL := good_Lf (J := J) a p
  have gL' := good_Lf (J := J) a p'
  have gQ := good_Qf (J := J) H p
  have gQ' := good_Qf (J := J) H p'
  have h3 := integral_sub ((gL.add gQ).mul (gL'.add gQ')).integrable
    (((gL.const_mul (-1)).add gQ).mul (gL'.add gQ')).integrable
  have h4 := integral_add ((gL.mul gL').integrable) ((gL.mul gQ').integrable)
  have h5 : ∀ W : J × Fin n → ℝ, (Lf a W p + Qf H W p) * (Lf a W p' + Qf H W p') -
      (-1 * Lf a W p + Qf H W p) * (Lf a W p' + Qf H W p') =
      2 * (Lf a W p * Lf a W p' + Lf a W p * Qf H W p') := by intro W; ring
  have h6 : ∀ W : J × Fin n → ℝ, (-1 * Lf a W p + Qf H W p) * (Lf a W p' + Qf H W p') =
      (-Lf a W p + Qf H W p) * (Lf a W p' + Qf H W p') := by intro W; ring

  simp_rw [h5] at h3
  simp_rw [h6] at h3
  rw [integral_const_mul, h4, w1, w2, int_LL] at h3
  have : nsq a = ∑ i, a i * a i := by
    unfold nsq; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this] at h3
  linarith

/-- `E[Q(p) Q(p')]`. -/
lemma int_QQ (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (p p' : J → ℝ) :
    ∫ W, Qf H W p * Qf H W p' ∂stdGauss (J × Fin n) =
      trH H ^ 2 * ((∑ q, p q ^ 2) * (∑ q, p' q ^ 2)) + 2 * frobH H * (∑ q, p q * p' q) ^ 2 := by
  have h := (wickTwoPoint J n 0 H hH p p').2
  simp only [Phi_split, Lf_zero, zero_add] at h
  rw [h]
  have : nsq (0 : Fin n → ℝ) = 0 := by simp [nsq]
  rw [this]; ring

/-- The two-point function with two different linear parts. -/
lemma int_two (a b : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (p p' : J → ℝ) :
    ∫ W, (Lf a W p + Qf H W p) * (Lf b W p' + Qf H W p') ∂stdGauss (J × Fin n) =
      (∑ i, a i * b i) * (∑ q, p q * p' q) +
        trH H ^ 2 * ((∑ q, p q ^ 2) * (∑ q, p' q ^ 2)) + 2 * frobH H * (∑ q, p q * p' q) ^ 2 := by
  have gL := good_Lf (J := J) a p
  have gL' := good_Lf (J := J) b p'
  have gQ := good_Qf (J := J) H p
  have gQ' := good_Qf (J := J) H p'
  have h : ∀ W : J × Fin n → ℝ, (Lf a W p + Qf H W p) * (Lf b W p' + Qf H W p') =
      (Lf a W p * Lf b W p' + Lf a W p * Qf H W p') +
        (Lf b W p' * Qf H W p + Qf H W p * Qf H W p') := by intro W; ring
  simp_rw [h]
  have e1 := integral_add (((gL.mul gL').add (gL.mul gQ')).integrable)
    (((gL'.mul gQ).add (gQ.mul gQ')).integrable)
  have e2 := integral_add ((gL.mul gL').integrable) ((gL.mul gQ').integrable)
  have e3 := integral_add ((gL'.mul gQ).integrable) ((gQ.mul gQ').integrable)

  rw [e1, e2, e3, int_LL, int_LQ a H hH, int_LQ b H hH, int_QQ H hH]
  ring

end gauss

/-! ## The separable form of `FA` -/

section sepform
variable {n : ℕ} {J : Type} [Fintype J]

/-- `FA = f(mu x) + a(x)·z + zᵀHz`. -/
lemma FA_split (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ) (W : J × Fin n → ℝ)
    (x : Fin n → ℝ) :
    FA f0 ℓ H mu ψ W x =
      qfun f0 ℓ H (mu x) + (Lf (aA ℓ H mu x) W (ψ x) + Qf H W (ψ x)) := by
  unfold FA qfun Lf Qf aA aU
  generalize mu x = m
  generalize zv W (ψ x) = z
  have h1 : ∑ i, ℓ i * (m i + z i) = ∑ i, ℓ i * m i + ∑ i, ℓ i * z i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, H i j * (m i + z i) * (m j + z j) =
      ∑ i, ∑ j, H i j * m i * m j + (∑ i, ∑ j, H i j * m j * z i + ∑ i, ∑ j, H i j * m i * z j)
        + ∑ i, ∑ j, H i j * z i * z j := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ i, ∑ j, H i j * m i * z j = ∑ i, ∑ j, H i j * m j * z i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : H j i = H i j := hH.apply i j
    rw [this]
  have h4 : ∑ i, (ℓ i + 2 * ∑ j, H i j * m j) * z i =
      ∑ i, ℓ i * z i + 2 * ∑ i, ∑ j, H i j * m j * z i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_mul, mul_assoc, Finset.sum_mul]
  rw [h1, h2, h3, h4]; ring

/-- Index of the terms of `FA`. -/
abbrev KKa (J : Type) (n : ℕ) := Unit ⊕ ((J × Fin n) ⊕ (J × J))

/-- Coefficients (polynomials in `W`). -/
def ccA (H : Matrix (Fin n) (Fin n) ℝ) (k : KKa J n) (W : J × Fin n → ℝ) : ℝ :=
  Sum.elim (fun _ => 1)
    (Sum.elim (fun β => W β) (fun qq => ∑ i, ∑ j, H i j * W (qq.1, i) * W (qq.2, j))) k

/-- Features (continuous functions of `x`). -/
def psA (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (mu : (Fin n → ℝ) → Fin n → ℝ)
    (ψ : (Fin n → ℝ) → J → ℝ) (k : KKa J n) (x : Fin n → ℝ) : ℝ :=
  Sum.elim (fun _ => qfun f0 ℓ H (mu x))
    (Sum.elim (fun β => aA ℓ H mu x β.2 * ψ x β.1) (fun qq => ψ x qq.1 * ψ x qq.2)) k

lemma FA_eq (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ) (W : J × Fin n → ℝ)
    (x : Fin n → ℝ) :
    FA f0 ℓ H mu ψ W x = ∑ k, ccA H k W * psA f0 ℓ H mu ψ k x := by
  rw [FA_split f0 ℓ H hH, Fintype.sum_sum_type, Fintype.sum_sum_type, Lf_eq]
  simp only [ccA, psA, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton,
    one_mul]
  congr 2
  · exact Finset.sum_congr rfl fun β _ => by ring
  · rw [Fintype.sum_prod_type]
    unfold Qf zv
    have h : ∀ i j : Fin n, H i j * (∑ q, W (q, i) * ψ x q) * (∑ q, W (q, j) * ψ x q) =
        ∑ q : J, ∑ q' : J, H i j * W (q, i) * W (q', j) * (ψ x q * ψ x q') := by
      intro i j
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q' _ => by ring
    simp_rw [h, Finset.sum_mul]
    exact BstLean.Part78.sum4 _

lemma good_ccA (H : Matrix (Fin n) (Fin n) ℝ) (k : KKa J n) :
    Good (stdGauss (J × Fin n)) (ccA H k) := by
  rcases k with u | β | qq
  · exact Good.const 1
  · exact good_coord β
  · show Good _ (fun W : J × Fin n → ℝ => ∑ i, ∑ j, H i j * W (qq.1, i) * W (qq.2, j))
    exact Good.sum _ fun i _ => Good.sum _ fun j _ =>
      ((good_coord (qq.1, i)).const_mul (H i j)).mul (good_coord (qq.2, j))

variable {f0 : ℝ} {ℓ : Fin n → ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
  {mu : (Fin n → ℝ) → Fin n → ℝ} {ψ : (Fin n → ℝ) → J → ℝ}

omit [Fintype J] in
lemma cont_psi (hψ : Continuous ψ) (q : J) : Continuous (fun x => ψ x q) :=
  (continuous_apply q).comp hψ

lemma cont_mu (hmu : Continuous mu) (i : Fin n) : Continuous (fun x => mu x i) :=
  (continuous_apply i).comp hmu

lemma cont_aA (hmu : Continuous mu) (i : Fin n) : Continuous (fun x => aA ℓ H mu x i) := by
  unfold aA aU
  exact continuous_const.add (continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul (cont_mu hmu j)))

lemma cont_qmu (hmu : Continuous mu) : Continuous (fun x => qfun f0 ℓ H (mu x)) := by
  unfold qfun
  exact (continuous_const.add (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (cont_mu hmu i))).add (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => (continuous_const.mul (cont_mu hmu i)).mul (cont_mu hmu j))

lemma cont_kA (hψ : Continuous ψ) : Continuous (kA ψ) :=
  continuous_finsetSum _ fun q _ => (cont_psi hψ q).pow 2

lemma cont_PhiA (hmu : Continuous mu) (hψ : Continuous ψ) : Continuous (PhiA f0 ℓ H mu ψ) :=
  (cont_qmu hmu).add (continuous_const.mul (cont_kA hψ))

lemma cont_KA (hψ : Continuous ψ) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => KA ψ z.1 z.2) :=
  continuous_finsetSum _ fun q _ =>
    ((cont_psi hψ q).comp continuous_fst).mul ((cont_psi hψ q).comp continuous_snd)

lemma cont_aaK (hmu : Continuous mu) (hψ : Continuous ψ) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (∑ i, aA ℓ H mu z.1 i * aA ℓ H mu z.2 i) * KA ψ z.1 z.2) :=
  (continuous_finsetSum _ fun i _ =>
    ((cont_aA hmu i).comp continuous_fst).mul ((cont_aA hmu i).comp continuous_snd)).mul
    (cont_KA hψ)

omit [Fintype J] in
lemma cont_psA (hmu : Continuous mu) (hψ : Continuous ψ) (k : KKa J n) :
    Continuous (psA f0 ℓ H mu ψ k) := by
  rcases k with u | β | qq
  · exact cont_qmu hmu
  · exact (cont_aA hmu β.2).mul (cont_psi hψ β.1)
  · exact (cont_psi hψ qq.1).mul (cont_psi hψ qq.2)

lemma cont_FA (hH : H.IsSymm) (hmu : Continuous mu) (hψ : Continuous ψ) (W : J × Fin n → ℝ) :
    Continuous (FA f0 ℓ H mu ψ W) := by
  have : FA f0 ℓ H mu ψ W = fun x => ∑ k, ccA H k W * psA f0 ℓ H mu ψ k x :=
    funext (FA_eq f0 ℓ H hH mu ψ W)
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (cont_psA hmu hψ k)

/-- `E_W F_W(x) = Φ(x)`. -/
lemma wickA1 (hH : H.IsSymm) (x : Fin n → ℝ) :
    ∫ W, FA f0 ℓ H mu ψ W x ∂stdGauss (J × Fin n) = PhiA f0 ℓ H mu ψ x := by
  simp_rw [FA_split f0 ℓ H hH]
  have e1 := integral_add (integrable_const (μ := stdGauss (J × Fin n)) (qfun f0 ℓ H (mu x)))
    (((good_Lf (aA ℓ H mu x) (ψ x)).add (good_Qf H (ψ x))).integrable)

  rw [e1, int_Phi _ H hH, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rfl

/-- `E_W F_W(x) F_W(y) = Φ(x)Φ(y) + a(x)·a(y) K(x,y) + 2‖H‖² K(x,y)²`. -/
lemma wickA2 (hH : H.IsSymm) (x y : Fin n → ℝ) :
    ∫ W, FA f0 ℓ H mu ψ W x * FA f0 ℓ H mu ψ W y ∂stdGauss (J × Fin n) =
      PhiA f0 ℓ H mu ψ x * PhiA f0 ℓ H mu ψ y +
        (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y + 2 * frobH H * KA ψ x y ^ 2 := by
  simp_rw [FA_split f0 ℓ H hH]
  set c := qfun f0 ℓ H (mu x)
  set c' := qfun f0 ℓ H (mu y)
  have gG := (good_Lf (J := J) (aA ℓ H mu x) (ψ x)).add (good_Qf H (ψ x))
  have gG' := (good_Lf (J := J) (aA ℓ H mu y) (ψ y)).add (good_Qf H (ψ y))
  have h : ∀ W : J × Fin n → ℝ,
      (c + (Lf (aA ℓ H mu x) W (ψ x) + Qf H W (ψ x))) *
        (c' + (Lf (aA ℓ H mu y) W (ψ y) + Qf H W (ψ y))) =
      (c * c' + c * (Lf (aA ℓ H mu y) W (ψ y) + Qf H W (ψ y))) +
        (c' * (Lf (aA ℓ H mu x) W (ψ x) + Qf H W (ψ x)) +
          (Lf (aA ℓ H mu x) W (ψ x) + Qf H W (ψ x)) *
            (Lf (aA ℓ H mu y) W (ψ y) + Qf H W (ψ y))) := by intro W; ring
  simp_rw [h]
  have e1 := integral_add (((Good.const (μ := stdGauss (J × Fin n)) (c * c')).add
    (gG'.const_mul c)).integrable) (((gG.const_mul c').add (gG.mul gG')).integrable)
  have e2 := integral_add (integrable_const (μ := stdGauss (J × Fin n)) (c * c'))
    ((gG'.const_mul c).integrable)
  have e3 := integral_add ((gG.const_mul c').integrable) ((gG.mul gG').integrable)

  have t0 : ∫ _ : J × Fin n → ℝ, c * c' ∂stdGauss (J × Fin n) = c * c' := by
    rw [integral_const]; simp only [probReal_univ, smul_eq_mul, one_mul]
  have t1 : ∫ W, c * (Lf (aA ℓ H mu y) W (ψ y) + Qf H W (ψ y)) ∂stdGauss (J × Fin n) =
      c * (trH H * ∑ q, ψ y q ^ 2) := by rw [integral_const_mul, int_Phi _ H hH]
  have t2 : ∫ W, c' * (Lf (aA ℓ H mu x) W (ψ x) + Qf H W (ψ x)) ∂stdGauss (J × Fin n) =
      c' * (trH H * ∑ q, ψ x q ^ 2) := by rw [integral_const_mul, int_Phi _ H hH]
  rw [e1, e2, e3, t0, t1, t2, int_two _ _ H hH]
  unfold PhiA KA kA
  ring

end sepform

/-! ## The identities -/

set_option maxHeartbeats 2000000 in
/-- **The exact conditional identities** (E) and (V). -/
theorem meanIdsA : MeanIdsA := by
  intro n J _ ν hν f0 ℓ H hH mu ψ hmu hψ
  have hprob := hν.prob
  set G := stdGauss (J × Fin n) with hG
  have ips : ∀ k, Integrable (psA f0 ℓ H mu ψ k) ν := fun k =>
    sphLaw_cont_integrable hν (cont_psA hmu hψ k)
  have ips2 : ∀ k l, Integrable (fun x => psA f0 ℓ H mu ψ k x * psA f0 ℓ H mu ψ l x) ν :=
    fun k l => sphLaw_cont_integrable hν ((cont_psA hmu hψ k).mul (cont_psA hmu hψ l))
  have hc1 : ∀ k : KKa J n, Integrable (ccA H k) G := fun k => (good_ccA H k).integrable
  have hc2 : ∀ k l : KKa J n, Integrable (fun W => ccA H k W * ccA H l W) G :=
    fun k l => ((good_ccA H k).mul (good_ccA H l)).integrable
  have intF_eq : ∀ W, ∫ x, FA f0 ℓ H mu ψ W x ∂ν =
      ∑ k, ccA H k W * ∫ x, psA f0 ℓ H mu ψ k x ∂ν := by
    intro W
    simp_rw [FA_eq f0 ℓ H hH]
    exact sep_int (fun k W => ccA H k W) (psA f0 ℓ H mu ψ) ips W
  have intF2_eq : ∀ W, ∫ x, FA f0 ℓ H mu ψ W x ^ 2 ∂ν =
      ∑ kl : KKa J n × KKa J n, (ccA H kl.1 W * ccA H kl.2 W) *
        ∫ x, psA f0 ℓ H mu ψ kl.1 x * psA f0 ℓ H mu ψ kl.2 x ∂ν := by
    intro W
    simp_rw [FA_eq f0 ℓ H hH]
    exact sep_int_sq (fun k W => ccA H k W) (psA f0 ℓ H mu ψ) ips2 W
  have VA_eq : ∀ W, VA ν f0 ℓ H mu ψ W =
      ∫ x, FA f0 ℓ H mu ψ W x ^ 2 ∂ν - (∫ x, FA f0 ℓ H mu ψ W x ∂ν) ^ 2 := by
    intro W
    unfold VA varU
    set m := ∫ y, FA f0 ℓ H mu ψ W y ∂ν with hm
    have h1 : Integrable (FA f0 ℓ H mu ψ W) ν := sphLaw_cont_integrable hν (cont_FA hH hmu hψ W)
    have h2 : Integrable (fun x => FA f0 ℓ H mu ψ W x ^ 2) ν :=
      sphLaw_cont_integrable hν ((cont_FA hH hmu hψ W).pow 2)
    have h : ∀ x, (FA f0 ℓ H mu ψ W x - m) ^ 2 =
        FA f0 ℓ H mu ψ W x ^ 2 - 2 * m * FA f0 ℓ H mu ψ W x + m ^ 2 := by intro x; ring
    simp_rw [h]
    have e1 := integral_add (h2.sub (h1.const_mul (2 * m))) (integrable_const (μ := ν) (m ^ 2))
    have e2 := integral_sub h2 (h1.const_mul (2 * m))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, ← hm]
    ring
  have gA' : Good G (fun W => ∫ x, FA f0 ℓ H mu ψ W x ∂ν) := by
    simp_rw [intF_eq]
    exact Good.sum _ fun k _ => (good_ccA H k).mul_const _
  have gB' : Good G (fun W => ∫ x, FA f0 ℓ H mu ψ W x ^ 2 ∂ν) := by
    simp_rw [intF2_eq]
    exact Good.sum _ fun kl _ => ((good_ccA H kl.1).mul (good_ccA H kl.2)).mul_const _
  have gV : Good G (VA ν f0 ℓ H mu ψ) := by
    have : VA ν f0 ℓ H mu ψ = fun W => ∫ x, FA f0 ℓ H mu ψ W x ^ 2 ∂ν -
        (∫ x, FA f0 ℓ H mu ψ W x ∂ν) ^ 2 := funext VA_eq
    rw [this]
    exact gB'.sub (gA'.pow 2)
  have gE : Good G (fun W => BA ν f0 ℓ H mu ψ W - gA ν f0 ℓ H mu ψ) := gA'.sub (Good.const _)
  -- continuity and integrability on the sphere
  have cΦ : Continuous (PhiA f0 ℓ H mu ψ) := cont_PhiA hmu hψ
  have iΦ : Integrable (PhiA f0 ℓ H mu ψ) ν := sphLaw_cont_integrable hν cΦ
  have iΦ2 : Integrable (fun x => PhiA f0 ℓ H mu ψ x ^ 2) ν := sphLaw_cont_integrable hν (cΦ.pow 2)
  -- exchanges of the integrals
  have E1 : ∫ W, ∫ x, FA f0 ℓ H mu ψ W x ∂ν ∂G = gA ν f0 ℓ H mu ψ := by
    have h : ∫ W, ∫ x, FA f0 ℓ H mu ψ W x ∂ν ∂G = ∫ x, ∫ W, FA f0 ℓ H mu ψ W x ∂G ∂ν := by
      simp_rw [FA_eq f0 ℓ H hH]
      exact sep_swap (μ := G) (ν := ν) (fun k W => ccA H k W) (psA f0 ℓ H mu ψ) hc1 ips
    rw [h]
    simp_rw [hG, wickA1 hH]
    rfl
  have E2 : ∫ W, ∫ x, FA f0 ℓ H mu ψ W x ^ 2 ∂ν ∂G =
      ∫ x, PhiA f0 ℓ H mu ψ x ^ 2 ∂ν + ∫ x, nsq (aA ℓ H mu x) * kA ψ x ∂ν +
        2 * frobH H * ∫ x, kA ψ x ^ 2 ∂ν := by
    have h : ∫ W, ∫ x, FA f0 ℓ H mu ψ W x ^ 2 ∂ν ∂G =
        ∫ x, ∫ W, FA f0 ℓ H mu ψ W x ^ 2 ∂G ∂ν := by
      simp_rw [FA_eq f0 ℓ H hH]
      exact sep_swap_sq (μ := G) (ν := ν) (fun k W => ccA H k W) (psA f0 ℓ H mu ψ) hc2 ips2
    rw [h]
    simp_rw [sq (FA f0 ℓ H mu ψ _ _), hG, wickA2 hH]
    have hd : ∀ x : Fin n → ℝ, PhiA f0 ℓ H mu ψ x * PhiA f0 ℓ H mu ψ x +
        (∑ i, aA ℓ H mu x i * aA ℓ H mu x i) * KA ψ x x + 2 * frobH H * KA ψ x x ^ 2 =
        PhiA f0 ℓ H mu ψ x ^ 2 + (nsq (aA ℓ H mu x) * kA ψ x + 2 * frobH H * kA ψ x ^ 2) := by
      intro x
      have h1 : KA ψ x x = kA ψ x := by
        unfold KA kA; exact Finset.sum_congr rfl fun q _ => by ring
      have h2 : ∑ i, aA ℓ H mu x i * aA ℓ H mu x i = nsq (aA ℓ H mu x) := by
        unfold nsq; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, h2]; ring
    simp_rw [hd]
    have cn : Continuous (fun x => nsq (aA ℓ H mu x) * kA ψ x) :=
      (continuous_finsetSum _ fun i _ => (cont_aA hmu i).pow 2).mul (cont_kA hψ)
    have i1 : Integrable (fun x => nsq (aA ℓ H mu x) * kA ψ x) ν := sphLaw_cont_integrable hν cn
    have i2 : Integrable (fun x => kA ψ x ^ 2) ν := sphLaw_cont_integrable hν ((cont_kA hψ).pow 2)
    have e1 := integral_add iΦ2 (i1.add (i2.const_mul (2 * frobH H)))
    have e2 := integral_add i1 (i2.const_mul (2 * frobH H))
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, integral_const_mul]
    ring
  have E3 : ∫ W, (∫ x, FA f0 ℓ H mu ψ W x ∂ν) ^ 2 ∂G =
      gA ν f0 ℓ H mu ψ ^ 2 + TaA ν ℓ H mu ψ + 2 * frobH H * S2A ν ψ := by
    have h : ∫ W, (∫ x, FA f0 ℓ H mu ψ W x ∂ν) ^ 2 ∂G =
        ∫ x, ∫ y, ∫ W, FA f0 ℓ H mu ψ W x * FA f0 ℓ H mu ψ W y ∂G ∂ν ∂ν := by
      simp_rw [FA_eq f0 ℓ H hH]
      exact sep_swap_two (μ := G) (ν := ν) (fun k W => ccA H k W) (psA f0 ℓ H mu ψ) hc2 ips
    rw [h]
    simp_rw [hG, wickA2 hH]
    have caK := cont_aaK (ℓ := ℓ) (H := H) hmu hψ
    have cK2 : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => KA ψ z.1 z.2 ^ 2) :=
      (cont_KA hψ).pow 2
    have hcaK : ∀ x : Fin n → ℝ,
        Continuous (fun y => (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y) := fun x =>
      (continuous_finsetSum _ fun i _ => continuous_const.mul (cont_aA hmu i)).mul
        (continuous_finsetSum _ fun q _ => continuous_const.mul (cont_psi hψ q))
    have hcK2 : ∀ x : Fin n → ℝ, Continuous (fun y => KA ψ x y ^ 2) := fun x =>
      (continuous_finsetSum _ fun q _ => continuous_const.mul (cont_psi hψ q)).pow 2
    have hin : ∀ x : Fin n → ℝ,
        ∫ y, (PhiA f0 ℓ H mu ψ x * PhiA f0 ℓ H mu ψ y +
          (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y + 2 * frobH H * KA ψ x y ^ 2) ∂ν =
        gA ν f0 ℓ H mu ψ * PhiA f0 ℓ H mu ψ x +
          (∫ y, (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y ∂ν +
            2 * frobH H * ∫ y, KA ψ x y ^ 2 ∂ν) := by
      intro x
      have j1 : Integrable (fun y => (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y) ν :=
        sphLaw_cont_integrable hν (hcaK x)
      have j2 : Integrable (fun y => KA ψ x y ^ 2) ν :=
        sphLaw_cont_integrable hν (hcK2 x)
      have hh : ∀ y : Fin n → ℝ, PhiA f0 ℓ H mu ψ x * PhiA f0 ℓ H mu ψ y +
          (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y + 2 * frobH H * KA ψ x y ^ 2 =
          PhiA f0 ℓ H mu ψ x * PhiA f0 ℓ H mu ψ y +
          ((∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y + 2 * frobH H * KA ψ x y ^ 2) := by
        intro y; ring
      simp_rw [hh]
      have e1 := integral_add (iΦ.const_mul (PhiA f0 ℓ H mu ψ x))
        (j1.add (j2.const_mul (2 * frobH H)))
      have e2 := integral_add j1 (j2.const_mul (2 * frobH H))
      simp only [Pi.add_apply] at e1 e2
      rw [e1, e2, integral_const_mul, integral_const_mul]
      unfold gA
      ring
    rw [funext hin]
    have k1 : Integrable (fun x => ∫ y, (∑ i, aA ℓ H mu x i * aA ℓ H mu y i) * KA ψ x y ∂ν) ν :=
      sphLaw_cont_integrable_right hν caK
    have k2 : Integrable (fun x => ∫ y, KA ψ x y ^ 2 ∂ν) ν :=
      sphLaw_cont_integrable_right hν cK2
    have e1 := integral_add (iΦ.const_mul (gA ν f0 ℓ H mu ψ))
      (k1.add (k2.const_mul (2 * frobH H)))
    have e2 := integral_add k1 (k2.const_mul (2 * frobH H))
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, integral_const_mul, integral_const_mul]
    unfold TaA S2A
    have : ∫ x, PhiA f0 ℓ H mu ψ x ∂ν = gA ν f0 ℓ H mu ψ := rfl
    rw [this]
    ring
  refine ⟨gV.integrable, (gV.pow 2).integrable, (gE.pow 2).integrable, ?_, ?_⟩
  · have h : ∀ W, (BA ν f0 ℓ H mu ψ W - gA ν f0 ℓ H mu ψ) ^ 2 =
        (∫ x, FA f0 ℓ H mu ψ W x ∂ν) ^ 2 -
          (2 * gA ν f0 ℓ H mu ψ) * (∫ x, FA f0 ℓ H mu ψ W x ∂ν) + gA ν f0 ℓ H mu ψ ^ 2 := by
      intro W; unfold BA; ring
    simp_rw [h]
    have e1 := integral_add (((gA'.pow 2).integrable).sub
      (gA'.integrable.const_mul (2 * gA ν f0 ℓ H mu ψ)))
      (integrable_const (μ := G) (gA ν f0 ℓ H mu ψ ^ 2))
    have e2 := integral_sub ((gA'.pow 2).integrable)
      (gA'.integrable.const_mul (2 * gA ν f0 ℓ H mu ψ))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const, E1, E3]
    simp only [probReal_univ, smul_eq_mul]
    ring
  · unfold VbarA
    simp_rw [VA_eq]
    rw [integral_sub gB'.integrable (gA'.pow 2).integrable, E2, E3]
    have hv : varU ν (PhiA f0 ℓ H mu ψ) =
        ∫ x, PhiA f0 ℓ H mu ψ x ^ 2 ∂ν - gA ν f0 ℓ H mu ψ ^ 2 := by
      unfold varU
      have hm : ∫ y, PhiA f0 ℓ H mu ψ y ∂ν = gA ν f0 ℓ H mu ψ := rfl
      rw [hm]
      set m := gA ν f0 ℓ H mu ψ
      have h : ∀ x, (PhiA f0 ℓ H mu ψ x - m) ^ 2 =
          PhiA f0 ℓ H mu ψ x ^ 2 - 2 * m * PhiA f0 ℓ H mu ψ x + m ^ 2 := by intro x; ring
      simp_rw [h]
      have e1 := integral_add (iΦ2.sub (iΦ.const_mul (2 * m))) (integrable_const (μ := ν) (m ^ 2))
      have e2 := integral_sub iΦ2 (iΦ.const_mul (2 * m))
      simp only [Pi.sub_apply] at e1
      rw [e1, e2, integral_const_mul, integral_const, hm]
      simp only [probReal_univ, smul_eq_mul]
      ring
    rw [hv]
    ring

end BstLean.Part80

#print axioms BstLean.Part80.sphLaw_cont_integrable
#print axioms BstLean.Part80.meanIdsA
