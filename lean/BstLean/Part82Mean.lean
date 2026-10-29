import BstLean.Part82Defs
import BstLean.Part78Mean3
import BstLean.Part78Wick

/-!
# Part 82: `regIface3` and `meanIds3`

`FG3 a H T W x = Σ_k cc3 T k ((a, H), W) * psi3 k x`, a finite separable sum over
`KK3 n = JJ3 n ⊕ (JJ3 n × JJ3 n) ⊕ (JJ3 n × JJ3 n × JJ3 n)`.
All integrals over the sphere and over the Gaussian are computed term by term.
The Wick identity `Wick3` is a hypothesis of `meanIds3`.
-/

namespace BstLean.Part82

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (Mono phiM varU)
open BstLean.Part78 (nsq frobH trH zv Good good_coord sph_int sep_int sep_int_sq sep_swap
  sep_swap_sq sep_swap_two sep_swap_cross)

variable {n : ℕ}

namespace MeanAux

/-! ## Features -/

lemma cont_pf3 (q : JJ3 n) : Continuous (fun x : Fin n → ℝ => pf3 x q) := by
  unfold pf3
  exact continuous_multiset_prod q.1.2.1 (fun i _ => continuous_apply i)

lemma cont_kap3_diag : Continuous (fun x : Fin n → ℝ => kap3 x x) :=
  continuous_finsetSum _ fun q _ => (cont_pf3 q).mul (cont_pf3 q)

lemma kap3_diag (x : Fin n → ℝ) : ∑ q : JJ3 n, pf3 x q ^ 2 = kap3 x x := by
  unfold kap3; exact Finset.sum_congr rfl fun q _ => by ring

/-! ## The separable form of `FG3` -/

/-- Index of the terms of `FG3`. -/
abbrev KK3 (n : ℕ) := JJ3 n ⊕ ((JJ3 n × JJ3 n) ⊕ (JJ3 n × JJ3 n × JJ3 n))

/-- The parameter space `((a, H), W)`. -/
abbrev Par (n : ℕ) := ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) × (WIdx3 n → ℝ)

/-- Coefficients (polynomials in `((a, H), W)`). -/
noncomputable def cc3 (T : T3 n) (k : KK3 n) (p : Par n) : ℝ :=
  Sum.elim (fun q => ∑ i, p.1.1 i * p.2 (q, i))
    (Sum.elim (fun qq => ∑ i, ∑ j, p.1.2 i j * p.2 (qq.1, i) * p.2 (qq.2, j))
      (fun qq => ∑ i, ∑ j, ∑ k, T i j k * p.2 (qq.1, i) * p.2 (qq.2.1, j) * p.2 (qq.2.2, k))) k

/-- Features (continuous functions of `x`). -/
noncomputable def psi3 (k : KK3 n) (x : Fin n → ℝ) : ℝ :=
  Sum.elim (fun q => pf3 x q)
    (Sum.elim (fun qq => pf3 x qq.1 * pf3 x qq.2)
      (fun qq => pf3 x qq.1 * pf3 x qq.2.1 * pf3 x qq.2.2)) k

lemma sum31 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm

lemma sum6 {A B C D E F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [Fintype F] (f : A → B → C → D → E → F → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g = ∑ d, ∑ e, ∑ g, ∑ a, ∑ b, ∑ c, f a b c d e g := by
  rw [sum31 (fun a b c d => ∑ e, ∑ g, f a b c d e g)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum31 (fun a b c e => ∑ g, f a b c d e g)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum31 (fun a b c g => f a b c d e g)]

lemma prod3 {J : Type*} [Fintype J] (t : ℝ) (f g h : J → ℝ) :
    t * (∑ q, f q) * (∑ q, g q) * (∑ q, h q) = ∑ q, ∑ q', ∑ q'', t * f q * g q' * h q'' := by
  have e1 : (∑ q, g q) * (∑ q, h q) = ∑ q', ∑ q'', g q' * h q'' := Finset.sum_mul_sum _ _ _ _
  calc t * (∑ q, f q) * (∑ q, g q) * (∑ q, h q)
      = ∑ q, (t * f q) * ((∑ q, g q) * (∑ q, h q)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    _ = _ := Finset.sum_congr rfl fun q _ => by
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q'' _ => by ring

instance : Fintype (KK3 n × KK3 n) := instFintypeProd _ _

lemma FG3_eq (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (W : WIdx3 n → ℝ)
    (x : Fin n → ℝ) :
    FG3 a H T W x = ∑ k, cc3 T k ((a, H), W) * psi3 k x := by
  unfold FG3 Phi3
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [cc3, psi3, Sum.elim_inl, Sum.elim_inr, zv, Fintype.sum_prod_type, add_assoc]
  congr 1
  · simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
  congr 1
  · have h : ∀ i j : Fin n, H i j * (∑ q, W (q, i) * pf3 x q) * (∑ q, W (q, j) * pf3 x q) =
        ∑ q : JJ3 n, ∑ q' : JJ3 n, H i j * W (q, i) * W (q', j) * (pf3 x q * pf3 x q') := by
      intro i j
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q' _ => by ring
    simp_rw [h, Finset.sum_mul]
    exact BstLean.Part78.sum4 _
  · have h : ∀ i j k : Fin n, T i j k * (∑ q, W (q, i) * pf3 x q) * (∑ q, W (q, j) * pf3 x q) *
          (∑ q, W (q, k) * pf3 x q) =
        ∑ q : JJ3 n, ∑ q' : JJ3 n, ∑ q'' : JJ3 n,
          T i j k * W (q, i) * W (q', j) * W (q'', k) * (pf3 x q * pf3 x q' * pf3 x q'') := by
      intro i j k
      rw [prod3]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ =>
        Finset.sum_congr rfl fun q'' _ => by ring
    simp_rw [h, Finset.sum_mul]
    exact sum6 _

lemma cont_psi3 (k : KK3 n) : Continuous (psi3 k) := by
  rcases k with q | qq | qq
  · exact cont_pf3 q
  · exact (cont_pf3 qq.1).mul (cont_pf3 qq.2)
  · exact ((cont_pf3 qq.1).mul (cont_pf3 qq.2.1)).mul (cont_pf3 qq.2.2)

lemma cont_cc3 (T : T3 n) (k : KK3 n) : Continuous (cc3 T k) := by
  rcases k with q | qq | qq
  · have : cc3 T (Sum.inl q) = fun p : Par n => ∑ i, p.1.1 i * p.2 (q, i) := rfl
    rw [this]; fun_prop
  · have : cc3 T (Sum.inr (Sum.inl qq)) =
        fun p : Par n => ∑ i, ∑ j, p.1.2 i j * p.2 (qq.1, i) * p.2 (qq.2, j) := rfl
    rw [this]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    have h : Continuous fun p : Par n => p.1.2 i j :=
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
    exact (h.mul (by fun_prop)).mul (by fun_prop)
  · have : cc3 T (Sum.inr (Sum.inr qq)) = fun p : Par n =>
        ∑ i, ∑ j, ∑ k, T i j k * p.2 (qq.1, i) * p.2 (qq.2.1, j) * p.2 (qq.2.2, k) := rfl
    rw [this]; fun_prop

lemma good_cc3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (k : KK3 n) :
    Good (stdGauss (WIdx3 n)) (fun W => cc3 T k ((a, H), W)) := by
  rcases k with q | qq | qq
  · simp only [cc3, Sum.elim_inl]
    exact Good.sum _ fun i _ => (good_coord (q, i)).const_mul (a i)
  · simp only [cc3, Sum.elim_inl, Sum.elim_inr]
    exact Good.sum _ fun i _ => Good.sum _ fun j _ =>
      ((good_coord (qq.1, i)).const_mul (H i j)).mul (good_coord (qq.2, j))
  · simp only [cc3, Sum.elim_inr]
    exact Good.sum _ fun i _ => Good.sum _ fun j _ => Good.sum _ fun k _ =>
      (((good_coord (qq.1, i)).const_mul (T i j k)).mul (good_coord (qq.2.1, j))).mul
        (good_coord (qq.2.2, k))

lemma int_psi3 (hn : 1 ≤ n) (k : KK3 n) : Integrable (psi3 k) (uniformSphere n) :=
  sph_int hn (cont_psi3 k)

lemma int_psi32 (hn : 1 ≤ n) (k l : KK3 n) :
    Integrable (fun x => psi3 k x * psi3 l x) (uniformSphere n) :=
  sph_int hn ((cont_psi3 k).mul (cont_psi3 l))

lemma cont_FG3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (W : WIdx3 n → ℝ) :
    Continuous (FG3 a H T W) := by
  have : FG3 a H T W = fun x => ∑ k, cc3 T k ((a, H), W) * psi3 k x := funext (FG3_eq a H T W)
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (cont_psi3 k)

lemma intF3_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) :
    ∫ x, FG3 a H T W x ∂uniformSphere n =
      ∑ k, cc3 T k ((a, H), W) * ∫ x, psi3 k x ∂uniformSphere n := by
  simp_rw [FG3_eq]
  exact sep_int (fun k (p : Par n) => cc3 T k p) psi3 (int_psi3 hn) ((a, H), W)

lemma intF32_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) :
    ∫ x, FG3 a H T W x ^ 2 ∂uniformSphere n =
      ∑ kl : KK3 n × KK3 n, (cc3 T kl.1 ((a, H), W) * cc3 T kl.2 ((a, H), W)) *
        ∫ x, psi3 kl.1 x * psi3 kl.2 x ∂uniformSphere n := by
  simp_rw [FG3_eq]
  exact sep_int_sq (fun k (p : Par n) => cc3 T k p) psi3 (int_psi32 hn) ((a, H), W)

lemma VG3_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) :
    VG3 a H T W =
      ∫ x, FG3 a H T W x ^ 2 ∂uniformSphere n - (∫ x, FG3 a H T W x ∂uniformSphere n) ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold VG3 varU
  set m := ∫ y, FG3 a H T W y ∂uniformSphere n with hm
  have h1 : Integrable (FG3 a H T W) (uniformSphere n) := sph_int hn (cont_FG3 a H T W)
  have h2 : Integrable (fun x => FG3 a H T W x ^ 2) (uniformSphere n) :=
    sph_int hn ((cont_FG3 a H T W).pow 2)
  have h : ∀ x, (FG3 a H T W x - m) ^ 2 = FG3 a H T W x ^ 2 - 2 * m * FG3 a H T W x + m ^ 2 := by
    intro x; ring
  simp_rw [h]
  have e1 := integral_add (h2.sub (h1.const_mul (2 * m)))
    (integrable_const (μ := uniformSphere n) (m ^ 2))
  have e2 := integral_sub h2 (h1.const_mul (2 * m))
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, ← hm]
  ring

/-! ## The Gaussian side -/

lemma wick31 (hW : Wick3) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (T : T3 n) (hT : SymT T) (x : Fin n → ℝ) :
    ∫ W, FG3 a H T W x ∂stdGauss (WIdx3 n) = trH H * kap3 x x := by
  have h := (hW (JJ3 n) n a H hH T hT (pf3 x) (pf3 x)).1
  rw [kap3_diag] at h
  exact h

lemma wick32 (hW : Wick3) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (T : T3 n) (hT : SymT T) (x y : Fin n → ℝ) :
    ∫ W, FG3 a H T W x * FG3 a H T W y ∂stdGauss (WIdx3 n) =
      C2 a H T (kap3 x x) (kap3 y y) (kap3 x y) := by
  have h := (hW (JJ3 n) n a H hH T hT (pf3 x) (pf3 y)).2
  rw [kap3_diag, kap3_diag] at h
  exact h

lemma good_zv {J : Type*} [Fintype J] (p : J → ℝ) (i : Fin n) :
    Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => zv W p i) :=
  Good.sum _ fun q _ => (good_coord (q, i)).mul_const (p q)

lemma good_Phi {J : Type*} [Fintype J] (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (p : J → ℝ) : Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => Part78.Phi a H W p) := by
  unfold Part78.Phi
  exact (Good.sum _ fun i _ => (good_zv p i).const_mul (a i)).add
    (Good.sum _ fun i _ => Good.sum _ fun j _ => ((good_zv p i).const_mul (H i j)).mul (good_zv p j))

lemma good_FG3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (x : Fin n → ℝ) :
    Good (stdGauss (WIdx3 n)) (fun W => FG3 a H T W x) := by
  simp_rw [FG3_eq]
  exact Good.sum _ fun k _ => (good_cc3 a H T k).mul_const _

lemma good_intF3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    Good (stdGauss (WIdx3 n)) (fun W => ∫ x, FG3 a H T W x ∂uniformSphere n) := by
  simp_rw [intF3_eq hn]
  exact Good.sum _ fun k _ => (good_cc3 a H T k).mul_const _

lemma gradF3_eq (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (W : WIdx3 n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    gradF3 a H T W x i = a i +
      Part78.Phi (fun j => 2 * H i j) (Matrix.of fun j k => 3 * T i j k) W (pf3 x) := by
  simp only [gradF3, Part78.Phi, Matrix.of_apply, Finset.mul_sum]
  rw [add_assoc]
  congr 2
  · exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The second moment of one component of the gradient. -/
lemma grad_sq (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hT : SymT T)
    (x : Fin n → ℝ) (i : Fin n) :
    ∫ W, gradF3 a H T W x i ^ 2 ∂stdGauss (WIdx3 n) =
      AA a T (kap3 x x) i ^ 2 + 4 * kap3 x x * ∑ j, H i j ^ 2 +
        18 * kap3 x x ^ 2 * ∑ j, ∑ k, T i j k ^ 2 := by
  set h : Fin n → ℝ := fun j => 2 * H i j with hh
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun j k => 3 * T i j k with hM
  have hsym : M.IsSymm := by
    ext j k
    simp only [hM, Matrix.transpose_apply, Matrix.of_apply]
    rw [(hT i j k).2]
  obtain ⟨w1, w2⟩ := Part78.wickTwoPoint (JJ3 n) n h M hsym (pf3 x) (pf3 x)
  rw [kap3_diag] at w1 w2
  have hkk : ∑ q : JJ3 n, pf3 x q * pf3 x q = kap3 x x := rfl
  rw [hkk] at w2
  have htr : trH M = 3 * trT T i := by
    simp only [trH, trT, hM, Matrix.of_apply, Finset.mul_sum]
  have hns : nsq h = 4 * ∑ j, H i j ^ 2 := by
    simp only [nsq, hh, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hfr : frobH M = 9 * ∑ j, ∑ k, T i j k ^ 2 := by
    simp only [frobH, hM, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have gP := good_Phi h M (pf3 x)
  have e : ∀ W : WIdx3 n → ℝ, gradF3 a H T W x i ^ 2 =
      a i ^ 2 + (2 * a i) * Part78.Phi h M W (pf3 x) +
        Part78.Phi h M W (pf3 x) * Part78.Phi h M W (pf3 x) := by
    intro W; rw [gradF3_eq]; ring
  simp_rw [e]
  have e1 := integral_add ((integrable_const (μ := stdGauss (WIdx3 n)) (a i ^ 2)).add
    (gP.integrable.const_mul (2 * a i))) (gP.mul gP).integrable
  have e2 := integral_add (integrable_const (μ := stdGauss (WIdx3 n)) (a i ^ 2))
    (gP.integrable.const_mul (2 * a i))
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const, w1, w2, htr, hns, hfr]
  simp only [probReal_univ, smul_eq_mul, AA]
  ring

lemma tau3_eq (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hT : SymT T)
    (x : Fin n → ℝ) :
    tau3 a H T x =
      ∑ i, AA a T (kap3 x x) i ^ 2 + 4 * kap3 x x * frobH H + 18 * kap3 x x ^ 2 * frobT T := by
  unfold tau3
  have gi : ∀ i, Good (stdGauss (WIdx3 n)) (fun W => gradF3 a H T W x i) := by
    intro i
    simp_rw [gradF3_eq]
    exact (Good.const _).add (good_Phi _ _ _)
  rw [integral_finsetSum _ fun i _ => ((gi i).pow 2).integrable]
  simp_rw [grad_sq a H T hT x]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- `w(x)` as a finite sum. -/
lemma wQ3_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (x : Fin n → ℝ) :
    wQ3 a H T x = ∑ kl : KK3 n × KK3 n,
      ((psi3 kl.1 x - ∫ y, psi3 kl.1 y ∂uniformSphere n) *
        (psi3 kl.2 x - ∫ y, psi3 kl.2 y ∂uniformSphere n)) *
        ∫ W, cc3 T kl.1 ((a, H), W) * cc3 T kl.2 ((a, H), W) ∂stdGauss (WIdx3 n) := by
  unfold wQ3
  have h : ∀ W, FG3 a H T W x - ∫ y, FG3 a H T W y ∂uniformSphere n =
      ∑ k, (psi3 k x - ∫ y, psi3 k y ∂uniformSphere n) * cc3 T k ((a, H), W) := by
    intro W
    rw [intF3_eq hn, FG3_eq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h]
  exact sep_int_sq (ν := stdGauss (WIdx3 n))
    (fun (k : KK3 n) (x : Fin n → ℝ) => psi3 k x - ∫ y, psi3 k y ∂uniformSphere n)
    (fun (k : KK3 n) (W : WIdx3 n → ℝ) => cc3 T k ((a, H), W))
    (fun k l => ((good_cc3 a H T k).mul (good_cc3 a H T l)).integrable) x

lemma cont_wQ3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    Continuous (wQ3 a H T) := by
  have : wQ3 a H T = fun x => _ := funext (wQ3_eq hn a H T)
  rw [this]
  exact continuous_finsetSum _ fun kl _ =>
    (((cont_psi3 kl.1).sub continuous_const).mul ((cont_psi3 kl.2).sub continuous_const)).mul
      continuous_const

lemma young (θ A E : ℝ) (hθ : 0 < θ) :
    (A - E) ^ 2 ≤ (1 + θ) * A ^ 2 + (1 + 1 / θ) * E ^ 2 := by
  have h : (1 + θ) * A ^ 2 + (1 + 1 / θ) * E ^ 2 - (A - E) ^ 2 = (θ * A + E) ^ 2 / θ := by
    field_simp; ring
  have : 0 ≤ (θ * A + E) ^ 2 / θ := by positivity
  linarith

end MeanAux

open MeanAux

local notation "γW" => stdGauss (WIdx3 _)

/-- **Regularity.** -/
theorem regIface3 (n : ℕ) (hn : 1 ≤ n) : RegIface3 n := by
  intro T
  have hA : Continuous (fun p : Par n => ∫ x, FG3 p.1.1 p.1.2 T p.2 x ∂uniformSphere n) := by
    simp_rw [intF3_eq hn]
    exact continuous_finsetSum _ fun k _ => (cont_cc3 T k).mul continuous_const
  have hB : Continuous (fun p : Par n => ∫ x, FG3 p.1.1 p.1.2 T p.2 x ^ 2 ∂uniformSphere n) := by
    simp_rw [intF32_eq hn]
    exact continuous_finsetSum _ fun kl _ =>
      ((cont_cc3 T kl.1).mul (cont_cc3 T kl.2)).mul continuous_const
  refine ⟨?_, ?_, fun a H W => cont_FG3 a H T W⟩
  · simp_rw [VG3_eq hn]
    exact hB.sub (hA.pow 2)
  · unfold errG3
    refine hA.sub (continuous_const.mul ?_)
    unfold trH
    exact continuous_finsetSum _ fun i _ =>
      (continuous_apply i).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))

/-- **The exact conditional identities.** -/
theorem meanIds3 (n : ℕ) (hn : 1 ≤ n) (hW : Wick3) : MeanIds3 n := by
  intro a H hH T hT
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  have gA : Good γW (fun W => ∫ x, FG3 a H T W x ∂uniformSphere n) := good_intF3 hn a H T
  have gB : Good γW (fun W => ∫ x, FG3 a H T W x ^ 2 ∂uniformSphere n) := by
    simp_rw [intF32_eq hn]
    exact Good.sum _ fun kl _ => ((good_cc3 a H T kl.1).mul (good_cc3 a H T kl.2)).mul_const _
  have gV : Good γW (VG3 a H T) := by
    have : VG3 a H T = fun W => ∫ x, FG3 a H T W x ^ 2 ∂uniformSphere n -
        (∫ x, FG3 a H T W x ∂uniformSphere n) ^ 2 := funext (VG3_eq hn a H T)
    rw [this]
    exact gB.sub (gA.pow 2)
  have gE : Good γW (errG3 a H T) := by
    have : errG3 a H T = fun W => ∫ x, FG3 a H T W x ∂uniformSphere n - 5 / 3 * trH H := rfl
    rw [this]
    exact gA.sub (Good.const _)
  have hc1 : ∀ k, Integrable (fun W => cc3 T k ((a, H), W)) γW :=
    fun k => (good_cc3 a H T k).integrable
  have hc2 : ∀ k l, Integrable (fun W => cc3 T k ((a, H), W) * cc3 T l ((a, H), W)) γW :=
    fun k l => ((good_cc3 a H T k).mul (good_cc3 a H T l)).integrable
  have E1 : ∫ W, ∫ x, FG3 a H T W x ∂uniformSphere n ∂γW = trH H * tG3 n := by
    have h : ∫ W, ∫ x, FG3 a H T W x ∂uniformSphere n ∂γW =
        ∫ x, ∫ W, FG3 a H T W x ∂γW ∂uniformSphere n := by
      simp_rw [FG3_eq]
      exact sep_swap (μ := γW) (ν := uniformSphere n) (fun k W => cc3 T k ((a, H), W)) psi3 hc1
        (int_psi3 hn)
    rw [h]
    simp_rw [wick31 hW a H hH T hT]
    rw [integral_const_mul]
    rfl
  have E2 : ∫ W, ∫ x, FG3 a H T W x ^ 2 ∂uniformSphere n ∂γW =
      ∫ x, C2 a H T (kap3 x x) (kap3 x x) (kap3 x x) ∂uniformSphere n := by
    have h : ∫ W, ∫ x, FG3 a H T W x ^ 2 ∂uniformSphere n ∂γW =
        ∫ x, ∫ W, FG3 a H T W x ^ 2 ∂γW ∂uniformSphere n := by
      simp_rw [FG3_eq]
      exact sep_swap_sq (μ := γW) (ν := uniformSphere n) (fun k W => cc3 T k ((a, H), W)) psi3 hc2
        (int_psi32 hn)
    rw [h]
    simp_rw [sq (FG3 a H T _ _), wick32 hW a H hH T hT]
  have E3 : ∫ W, (∫ x, FG3 a H T W x ∂uniformSphere n) ^ 2 ∂γW =
      ∫ x, ∫ y, C2 a H T (kap3 x x) (kap3 y y) (kap3 x y) ∂uniformSphere n ∂uniformSphere n := by
    have h : ∫ W, (∫ x, FG3 a H T W x ∂uniformSphere n) ^ 2 ∂γW =
        ∫ x, ∫ y, ∫ W, FG3 a H T W x * FG3 a H T W y ∂γW ∂uniformSphere n ∂uniformSphere n := by
      simp_rw [FG3_eq]
      exact sep_swap_two (μ := γW) (ν := uniformSphere n) (fun k W => cc3 T k ((a, H), W)) psi3 hc2
        (int_psi3 hn)
    rw [h]
    simp_rw [wick32 hW a H hH T hT]
  have I5 : ∫ W, errG3 a H T W ^ 2 ∂γW =
      (∫ x, ∫ y, C2 a H T (kap3 x x) (kap3 y y) (kap3 x y) ∂uniformSphere n ∂uniformSphere n) -
        10 / 3 * trH H ^ 2 * tG3 n + 25 / 9 * trH H ^ 2 := by
    have h : ∀ W, errG3 a H T W ^ 2 = (∫ x, FG3 a H T W x ∂uniformSphere n) ^ 2 -
        (2 * (5 / 3 * trH H)) * (∫ x, FG3 a H T W x ∂uniformSphere n) + (5 / 3 * trH H) ^ 2 := by
      intro W; unfold errG3; ring
    simp_rw [h]
    have e1 := integral_add
      (((gA.pow 2).integrable).sub (gA.integrable.const_mul (2 * (5 / 3 * trH H))))
      (integrable_const (μ := γW) ((5 / 3 * trH H) ^ 2))
    have e2 := integral_sub ((gA.pow 2).integrable)
      (gA.integrable.const_mul (2 * (5 / 3 * trH H)))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const, E1, E3]
    simp only [probReal_univ, smul_eq_mul]
    ring
  have I6 : ∀ x : Fin n → ℝ, ∫ W, (FG3 a H T W x - 5 / 3 * trH H) ^ 2 ∂γW =
      C2 a H T (kap3 x x) (kap3 x x) (kap3 x x) - 10 / 3 * trH H ^ 2 * kap3 x x +
        25 / 9 * trH H ^ 2 := by
    intro x
    have gF := good_FG3 a H T x
    have h : ∀ W, (FG3 a H T W x - 5 / 3 * trH H) ^ 2 = FG3 a H T W x * FG3 a H T W x -
        (2 * (5 / 3 * trH H)) * FG3 a H T W x + (5 / 3 * trH H) ^ 2 := by
      intro W; ring
    simp_rw [h]
    have e1 := integral_add
      (((gF.mul gF).integrable).sub (gF.integrable.const_mul (2 * (5 / 3 * trH H))))
      (integrable_const (μ := γW) ((5 / 3 * trH H) ^ 2))
    have e2 := integral_sub ((gF.mul gF).integrable)
      (gF.integrable.const_mul (2 * (5 / 3 * trH H)))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const, wick31 hW a H hH T hT,
      wick32 hW a H hH T hT]
    simp only [probReal_univ, smul_eq_mul]
    ring
  refine ⟨gV.integrable, (gV.pow 2).integrable, (gE.pow 2).integrable, ?_, I5, I6, ?_,
    tau3_eq a H T hT, cont_wQ3 hn a H T, ?_⟩
  · simp_rw [VG3_eq hn]
    rw [integral_sub gB.integrable (gA.pow 2).integrable, E2, E3]
  · intro x θ hθ
    have gF := good_FG3 a H T x
    have g1 : Integrable (fun W => (FG3 a H T W x - 5 / 3 * trH H) ^ 2) γW :=
      ((gF.sub (Good.const _)).pow 2).integrable
    have g2 : Integrable (fun W => errG3 a H T W ^ 2) γW := (gE.pow 2).integrable
    have g3 : Integrable
        (fun W => (FG3 a H T W x - ∫ y, FG3 a H T W y ∂uniformSphere n) ^ 2) γW :=
      ((gF.sub gA).pow 2).integrable
    have hle : ∫ W, (FG3 a H T W x - ∫ y, FG3 a H T W y ∂uniformSphere n) ^ 2 ∂γW ≤
        ∫ W, ((1 + θ) * (FG3 a H T W x - 5 / 3 * trH H) ^ 2 +
          (1 + 1 / θ) * errG3 a H T W ^ 2) ∂γW := by
      refine integral_mono g3 ((g1.const_mul _).add (g2.const_mul _)) fun W => ?_
      have := young θ (FG3 a H T W x - 5 / 3 * trH H) (errG3 a H T W) hθ
      have e : FG3 a H T W x - 5 / 3 * trH H - errG3 a H T W =
          FG3 a H T W x - ∫ y, FG3 a H T W y ∂uniformSphere n := by unfold errG3; ring
      rw [e] at this
      exact this
    have e1 := integral_add (g1.const_mul (1 + θ)) (g2.const_mul (1 + 1 / θ))
    rw [e1, integral_const_mul, integral_const_mul] at hle
    exact hle
  · have : tau3 a H T = fun x => _ := funext (tau3_eq a H T hT)
    rw [this]
    refine ((continuous_finsetSum _ fun i _ => ?_).add
      ((continuous_const.mul cont_kap3_diag).mul continuous_const)).add
      ((continuous_const.mul (cont_kap3_diag.pow 2)).mul continuous_const)
    unfold AA
    exact (continuous_const.add ((continuous_const.mul cont_kap3_diag).mul continuous_const)).pow 2

end BstLean.Part82

#print axioms BstLean.Part82.regIface3
#print axioms BstLean.Part82.meanIds3
