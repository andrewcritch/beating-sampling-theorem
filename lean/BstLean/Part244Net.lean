import BstLean.Part244Gordon
import BstLean.Part208Smin

/-! Part 244: finite Euclidean nets of the unit sphere, and the two net estimates used to pass
from Gordon's finite comparison to the smallest singular value. -/
namespace BstLean.Part244
open MeasureTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg e0)
open BstLean.Part152 (opN opN_nonneg mulVec_le_opN dot_le_norm)
open BstLean.Part153 (nrm nrm_nonneg)
open BstLean.Part208 (minStretch minStretchSet minStretch_le)

/-- A finite `ε`-net of the Euclidean unit sphere, made of unit vectors. -/
def IsNet {d : ℕ} (V : Finset (Fin d → ℝ)) (ε : ℝ) : Prop :=
  (∀ x ∈ V, normSq x = 1) ∧ ∀ y : Fin d → ℝ, normSq y = 1 → ∃ x ∈ V, normSq (y - x) ≤ ε ^ 2

lemma isCompact_sphere' (d : ℕ) : IsCompact {y : Fin d → ℝ | normSq y = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by unfold normSq; fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := 1)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h1 : y i ^ 2 ≤ normSq y :=
      Finset.single_le_sum (f := fun i => y i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hy] at h1
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

/-- Finite nets exist for every positive radius. -/
theorem exists_net {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Finset (Fin d → ℝ), V.Nonempty ∧ IsNet V ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_sphere' d)
    (e := ε / √d) (by positivity)
  have hcl : ∀ y ∈ {y : Fin d → ℝ | normSq y = 1}, ∃ x ∈ htf.toFinset, normSq (y - x) ≤ ε ^ 2 := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcov hy)
    refine ⟨x, htf.mem_toFinset.mpr hx, ?_⟩
    rw [Metric.mem_ball] at hyx
    have hc : ∀ i, (y - x) i ^ 2 ≤ (ε / √d) ^ 2 := by
      intro i
      have h1 : dist (y i) (x i) ≤ dist y x := dist_le_pi_dist y x i
      rw [Real.dist_eq] at h1
      have h2 : |(y - x) i| ≤ ε / √d := by
        simp only [Pi.sub_apply]; linarith
      exact sq_le_sq' (by linarith [abs_nonneg ((y - x) i), neg_abs_le ((y - x) i)])
        ((le_abs_self _).trans h2)
    calc normSq (y - x) = ∑ i, (y - x) i ^ 2 := rfl
      _ ≤ ∑ _i : Fin d, (ε / √d) ^ 2 := Finset.sum_le_sum fun i _ => hc i
      _ = ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow,
          Real.sq_sqrt hdR.le]
        field_simp
  refine ⟨htf.toFinset, ?_, fun x hx => hts (htf.mem_toFinset.mp hx), fun y hy => hcl y hy⟩
  obtain ⟨x, hx, -⟩ := hcl (e0 d) (BstLean.Part130.normSq_e0 hd)
  exact ⟨x, hx⟩

lemma nrm_eq_sqrt {d : ℕ} (w : Fin d → ℝ) : nrm w = √(∑ i, w i ^ 2) := rfl

lemma abs_dot_le {d : ℕ} (a w : Fin d → ℝ) : |a ⬝ᵥ w| ≤ nrm a * nrm w := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a w
  have e : nrm a * nrm w = √((∑ i, a i ^ 2) * ∑ i, w i ^ 2) := by
    unfold nrm normSq
    rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [e]
  exact Real.abs_le_sqrt h

/-- The smallest singular value is at least the net minimum minus `ε` times the operator norm. -/
theorem minStretch_ge_net {N d : ℕ} (hd : 1 ≤ d) {V : Finset (Fin d → ℝ)} (hV : V.Nonempty)
    {ε : ℝ} (hε : 0 ≤ ε) (hnet : IsNet V ε) (M : Matrix (Fin N) (Fin d) ℝ) :
    V.inf' hV (fun x => nrm (M *ᵥ x)) - ε * opN M ≤ minStretch M := by
  apply le_csInf (BstLean.Part208.minStretchSet_nonempty hd M)
  rintro r ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := hnet.2 y hy
  have h1 : V.inf' hV (fun x => nrm (M *ᵥ x)) ≤ nrm (M *ᵥ x) := Finset.inf'_le _ hx
  have h2 : nrm (M *ᵥ x) ≤ nrm (M *ᵥ y) + nrm (M *ᵥ (x - y)) := by
    have e : M *ᵥ x = M *ᵥ y + M *ᵥ (x - y) := by rw [← Matrix.mulVec_add]; congr 1; abel
    rw [e]
    exact BstLean.Part153.nrm_add_le _ _
  have h3 : nrm (M *ᵥ (x - y)) ≤ opN M * nrm (x - y) := mulVec_le_opN M (x - y)
  have h4 : nrm (x - y) ≤ ε := by
    have e : normSq (x - y) = normSq (y - x) := by
      unfold normSq; exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
    unfold nrm
    rw [e]
    exact Real.sqrt_le_iff.mpr ⟨hε, hyx⟩
  have h5 := mul_le_mul_of_nonneg_left h4 (opN_nonneg M)
  linarith

/-- The net maximum of a linear form is at least `(1 - ε)` times the norm. -/
theorem net_max_ge {d : ℕ} {U : Finset (Fin d → ℝ)} (hU : U.Nonempty) {ε : ℝ}
    (hnet : IsNet U ε) (hε : 0 ≤ ε) (w : Fin d → ℝ) :
    (1 - ε) * nrm w ≤ U.sup' hU (fun u => u ⬝ᵥ w) := by
  by_cases hw : normSq w = 0
  · have h0 : nrm w = 0 := by unfold nrm; rw [hw, Real.sqrt_zero]
    rw [h0, mul_zero]
    obtain ⟨u, hu⟩ := hU
    have hw0 : w = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j))).1 hw i
        (Finset.mem_univ i)
      simpa using this
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun u => u ⬝ᵥ w) hu)
    simp [hw0]
  · have hpos : 0 < nrm w := Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg w) (Ne.symm hw))
    set ŵ := (nrm w)⁻¹ • w with hŵ
    have hŵ1 : normSq ŵ = 1 := by
      rw [hŵ, BstLean.Part130.normSq_smul, inv_pow, BstLean.Part153.nrm_sq,
        inv_mul_cancel₀ (by positivity)]
    obtain ⟨u, hu, hdist⟩ := hnet.2 ŵ hŵ1
    have hdot : ŵ ⬝ᵥ w = nrm w := by
      rw [hŵ, smul_dotProduct, smul_eq_mul]
      have : w ⬝ᵥ w = nrm w ^ 2 := by
        rw [BstLean.Part153.nrm_sq]; unfold normSq dotProduct; simp [sq]
      rw [this]; field_simp
    have hcs := abs_dot_le (ŵ - u) w
    have hn : nrm (ŵ - u) ≤ ε := by unfold nrm; exact Real.sqrt_le_iff.mpr ⟨hε, hdist⟩
    have hsplit : u ⬝ᵥ w = ŵ ⬝ᵥ w - (ŵ - u) ⬝ᵥ w := by rw [sub_dotProduct]; ring
    have h1 : u ⬝ᵥ w ≤ U.sup' hU (fun u => u ⬝ᵥ w) := Finset.le_sup' (fun u => u ⬝ᵥ w) hu
    have h2 := mul_le_mul_of_nonneg_right hn (nrm_nonneg w)
    have h3 := (abs_le.mp hcs).2
    nlinarith

/-- A separable min–max is at least the row minimum plus the column maximum. -/
theorem minmax_sep_ge {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (g : I → ℝ) (f : J → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty g + Finset.univ.sup' Finset.univ_nonempty f ≤
      minmax (fun s : I × J => g s.1 + f s.2) := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := J)) f
  unfold minmax
  refine Finset.le_inf' _ _ fun i _ => ?_
  have h1 : Finset.univ.inf' Finset.univ_nonempty g ≤ g i := Finset.inf'_le _ (Finset.mem_univ i)
  have h2 : g i + f j0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => g i + f j) :=
    Finset.le_sup' (fun j => g i + f j) (Finset.mem_univ j0)
  simp only at h2 ⊢
  rw [hj0]
  linarith

end BstLean.Part244
