import BstLean.Part81Defs
import BstLean.Part78Mean

/-!
# Part 81: generic kernel facts (`KerGen`), every map degree
-/

namespace BstLean.Part81.KG

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part78 (sph_int sep_int sep_int_sq)
open BstLean.Part81

variable {n d : ℕ}

lemma cont_pf (q : JJ n d) : Continuous (fun x : Fin n → ℝ => pf x q) := by
  unfold pf
  exact continuous_multiset_prod q.1.2.1 (fun i _ => continuous_apply i)

/-- The mean feature. -/
noncomputable def mu (n d : ℕ) (q : JJ n d) : ℝ := ∫ y, pf y q ∂uniformSphere n

lemma cont_kap_diag : Continuous (fun x : Fin n → ℝ => kap d x x) :=
  continuous_finsetSum _ fun q _ => (cont_pf q).mul (cont_pf q)

lemma cont_kap_right (x : Fin n → ℝ) : Continuous (fun y : Fin n → ℝ => kap d x y) :=
  continuous_finsetSum _ fun q _ => continuous_const.mul (cont_pf q)

lemma kap_int (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∫ y, kap d x y ∂uniformSphere n = ∑ q : JJ n d, pf x q * mu n d q :=
  sep_int (fun (q : JJ n d) (x : Fin n → ℝ) => pf x q)
    (fun (q : JJ n d) (y : Fin n → ℝ) => pf y q) (fun q => sph_int hn (cont_pf q)) x

lemma cont_kap_int2 (hn : 1 ≤ n) :
    Continuous (fun x : Fin n → ℝ => ∫ y, kap d x y ^ 2 ∂uniformSphere n) := by
  have h : ∀ x : Fin n → ℝ, ∫ y, kap d x y ^ 2 ∂uniformSphere n =
      ∑ kl : JJ n d × JJ n d, (pf x kl.1 * pf x kl.2) *
        ∫ y, pf y kl.1 * pf y kl.2 ∂uniformSphere n := fun x =>
    sep_int_sq (fun (q : JJ n d) (x : Fin n → ℝ) => pf x q)
      (fun (q : JJ n d) (y : Fin n → ℝ) => pf y q)
      (fun q q' => sph_int hn ((cont_pf q).mul (cont_pf q'))) x
  simp_rw [h]
  exact continuous_finsetSum _ fun kl _ =>
    ((cont_pf kl.1).mul (cont_pf kl.2)).mul continuous_const

lemma mm1_eq (hn : 1 ≤ n) : mm1 n d = ∑ q : JJ n d, mu n d q ^ 2 := by
  unfold mm1
  simp_rw [kap_int hn]
  rw [integral_finsetSum _ (fun q _ => (sph_int hn (cont_pf q)).mul_const _)]
  simp_rw [integral_mul_const, sq]
  rfl

/-- `(E f)² ≤ E f²` on the sphere. -/
lemma sq_int_le (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂uniformSphere n) ^ 2 ≤ ∫ x, f x ^ 2 ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  set m := ∫ x, f x ∂uniformSphere n with hm
  have h1 : Integrable f (uniformSphere n) := sph_int hn hf
  have h2 : Integrable (fun x => f x ^ 2) (uniformSphere n) := sph_int hn (hf.pow 2)
  have h0 : 0 ≤ ∫ x, (f x - m) ^ 2 ∂uniformSphere n :=
    integral_nonneg fun x => sq_nonneg _
  have h : ∀ x, (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 := by
    intro x; ring
  simp_rw [h] at h0
  have e1 := integral_add (h2.sub (h1.const_mul (2 * m)))
    (integrable_const (μ := uniformSphere n) (m ^ 2))
  have e2 := integral_sub h2 (h1.const_mul (2 * m))
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, integral_const_mul, integral_const] at h0
  simp only [probReal_univ, smul_eq_mul, ← hm] at h0
  nlinarith

end BstLean.Part81.KG

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part78 (sph_int sep_int sep_int_sq)
open BstLean.Part81.KG

theorem k1_sq_le (n d : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) :
    (∫ y, kap d x y ∂uniformSphere n) ^ 2 ≤ kap d x x * mm1 n d := by
  rw [kap_int hn, mm1_eq hn]
  have h : kap d x x = ∑ q : JJ n d, pf x q ^ 2 := by
    unfold kap; exact Finset.sum_congr rfl fun q _ => (sq _).symm
  rw [h]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem k2_le (n d : ℕ) (hn : 1 ≤ n) (CF : ℝ) (hF : FeatOp n d CF) (x : Fin n → ℝ) :
    ∫ y, kap d x y ^ 2 ∂uniformSphere n ≤ CF / (n : ℝ) * kap d x x := by
  have h : kap d x x = ∑ q : JJ n d, pf x q ^ 2 := by
    unfold kap; exact Finset.sum_congr rfl fun q _ => (sq _).symm
  rw [h]
  exact hF (fun q => pf x q)

theorem kerGen (n d : ℕ) (hn : 1 ≤ n) : KerGen n d := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hm0 : 0 ≤ mm1 n d := by
    rw [mm1_eq hn]; exact Finset.sum_nonneg fun q _ => sq_nonneg _
  refine ⟨hm0, ?_, ?_, ?_⟩
  · exact integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _
  · exact sq_int_le hn cont_kap_diag
  · intro CF hCF hF
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · have hc : Continuous (fun x : Fin n → ℝ => ∑ q : JJ n d, mu n d q * pf x q) :=
        continuous_finsetSum _ fun q _ => continuous_const.mul (cont_pf q)
      have h1 := sq_int_le hn hc
      have h2 := hF (mu n d)
      have h3 : ∫ x, ∑ q : JJ n d, mu n d q * pf x q ∂uniformSphere n = mm1 n d := by
        rw [integral_finsetSum _ (fun q _ => (sph_int hn (cont_pf q)).const_mul _), mm1_eq hn]
        simp_rw [integral_const_mul, sq]
        rfl
      rw [h3] at h1
      rw [← mm1_eq hn] at h2
      have h4 : mm1 n d * mm1 n d ≤ CF / (n : ℝ) * mm1 n d := by nlinarith
      rcases hm0.eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact le_of_mul_le_mul_right h4 h0
    · unfold ss2 tG
      rw [← integral_const_mul]
      exact integral_mono (sph_int hn (cont_kap_int2 hn))
        ((sph_int hn cont_kap_diag).const_mul _) (fun x => k2_le n d hn CF hF x)

end BstLean.Part81

#print axioms BstLean.Part81.kerGen
#print axioms BstLean.Part81.k1_sq_le
#print axioms BstLean.Part81.k2_le
