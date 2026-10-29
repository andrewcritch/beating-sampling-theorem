import BstLean.Part218Angular
import BstLean.Part33Moments
import BstLean.Part105Law
import BstLean.Part36Defs

/-! Explicit second and fourth angular moments for the covariance remainder. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part33 BstLean.Part36 BstLean.Part105 BstLean.Part130

noncomputable def angularMoment (N k : ℕ) : ℝ := gaussMom (2 * k) / rhoD N k

theorem sphere_coordinate_even {N : ℕ} (hN : 1 ≤ N) (i : Fin N) (k : ℕ) :
    (∫ u : Fin N → ℝ, u i ^ (2 * k) ∂uniformSphere N) = angularMoment N k := by
  classical
  have h := (uniformSphere_prod N (2 * k) hN).mom (2 * k) le_rfl (fun _ => i)
  have he : (∏ j : Fin N, gaussMom ((Finset.univ.filter (fun _s : Fin (2 * k) => i = j)).card)) =
      gaussMom (2 * k) := by
    have hp : ∀ j : Fin N, gaussMom ((Finset.univ.filter (fun _s : Fin (2 * k) => i = j)).card) =
        if j = i then gaussMom (2 * k) else 1 := by
      intro j
      by_cases hj : j = i
      · subst j; simp
      · simp [Ne.symm hj, hj, gaussMom]
    simp_rw [hp]
    simp
  rw [he] at h
  simpa [angularMoment, rhoD] using h

noncomputable def angularA (N : ℕ) : ℝ := 1 / (4 * π * N)
noncomputable def angularB (N : ℕ) : ℝ := (1 / 2 - 3 / (2 * π)) / (2 * N)
noncomputable def angularK (N : ℕ) (e x : ℝ) : ℝ := angularG x / (2 * N) + e

lemma angularB_nonneg (N : ℕ) : 0 ≤ angularB N := by
  have hp := pi_gt_three
  have h : 3 / (2 * π) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * π)).mpr
    linarith
  unfold angularB
  positivity

lemma angularK_decomp {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ angularG x / (2 * N) - angularA N * x ^ 2 ∧
    angularG x / (2 * N) - angularA N * x ^ 2 ≤ angularB N * x ^ 4 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hl, hu⟩ := angularG_envelope hx
  have hl' := div_le_div_of_nonneg_right hl (by positivity : 0 ≤ 2 * (N : ℝ))
  have hu' := div_le_div_of_nonneg_right hu (by positivity : 0 ≤ 2 * (N : ℝ))
  have h1 : x ^ 2 / (2 * π) / (2 * (N : ℝ)) = angularA N * x ^ 2 := by unfold angularA; ring
  have h2 : (x ^ 2 / (2 * π) + (1 / 2 - 3 / (2 * π)) * x ^ 4) / (2 * (N : ℝ)) =
      angularA N * x ^ 2 + angularB N * x ^ 4 := by unfold angularA angularB; ring
  rw [h1] at hl'
  rw [h2] at hu'
  constructor <;> linarith

lemma angularK_square_bound {N : ℕ} (hN : 1 ≤ N) {e x : ℝ} (he : e ≤ 0) (hx : |x| ≤ 1) :
    angularK N e x ^ 2 ≤ angularA N ^ 2 * x ^ 4 + 2 * angularA N * e * x ^ 2 + e ^ 2 +
      2 * angularA N * angularB N * x ^ 6 + angularB N ^ 2 * x ^ 8 := by
  let d := angularG x / (2 * N) - angularA N * x ^ 2
  obtain ⟨hd0, hd1⟩ := angularK_decomp hN hx
  have ha : 0 ≤ angularA N := by unfold angularA; positivity
  have hb := angularB_nonneg N
  have h2 := pow_le_pow_left₀ hd0 hd1 2
  have h3 := mul_le_mul_of_nonneg_left hd1 (show 0 ≤ 2 * angularA N * x ^ 2 by positivity)
  have h4 := mul_nonpos_of_nonpos_of_nonneg he hd0
  have hk : angularK N e x = angularA N * x ^ 2 + e + d := by dsimp [angularK, d]; ring
  rw [hk]
  change 0 ≤ d at hd0
  change d ≤ angularB N * x ^ 4 at hd1
  change d ^ 2 ≤ (angularB N * x ^ 4) ^ 2 at h2
  change 2 * angularA N * x ^ 2 * d ≤ _ at h3
  change e * d ≤ 0 at h4
  nlinarith

lemma angularK_four_bound {N : ℕ} (hN : 1 ≤ N) {e x : ℝ} (hx : |x| ≤ 1) :
    angularK N e x ^ 4 ≤ (angularA N * x ^ 2 + |e| + angularB N * x ^ 4) ^ 4 := by
  obtain ⟨hd0, hd1⟩ := angularK_decomp hN hx
  have ha : 0 ≤ angularA N := by unfold angularA; positivity
  have hb := angularB_nonneg N
  have hg : 0 ≤ angularG x / (2 * N) := by nlinarith [mul_nonneg ha (sq_nonneg x)]
  have hk : |angularK N e x| ≤ angularA N * x ^ 2 + |e| + angularB N * x ^ 4 := by
    unfold angularK
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hg]; linarith)
  have h := pow_le_pow_left₀ (abs_nonneg _) hk 4
  simpa only [pow_abs, abs_pow, abs_of_nonneg (show 0 ≤ angularK N e x ^ 4 by positivity)] using h

noncomputable def angularJ2 (N : ℕ) (e : ℝ) : ℝ :=
  angularA N ^ 2 * angularMoment N 2 + 2 * angularA N * e * angularMoment N 1 + e ^ 2 +
    2 * angularA N * angularB N * angularMoment N 3 + angularB N ^ 2 * angularMoment N 4

noncomputable def angularJ4 (N : ℕ) (e : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ l ∈ Finset.range (5 - i),
    (Nat.choose 4 i : ℝ) * (Nat.choose (4 - i) l : ℝ) * angularA N ^ i * |e| ^ (4 - i - l) *
      angularB N ^ l * angularMoment N (i + 2 * l)

lemma sphere_coordinate_abs {N : ℕ} {u : Fin N → ℝ} (hu : normSq u = 1) (i : Fin N) : |u i| ≤ 1 := by
  have h : u i ^ 2 ≤ normSq u := Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  rw [hu] at h
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

lemma angular_second_polynomial_integral {N : ℕ} (hN : 1 ≤ N) (i : Fin N) (e : ℝ) :
    (∫ u : Fin N → ℝ, angularA N ^ 2 * u i ^ 4 + 2 * angularA N * e * u i ^ 2 + e ^ 2 +
      2 * angularA N * angularB N * u i ^ 6 + angularB N ^ 2 * u i ^ 8 ∂uniformSphere N) =
      angularJ2 N e := by
  have := uniformSphere_isProbability N hN
  have ip (k : ℕ) : Integrable (fun u : Fin N → ℝ => u i ^ k) (uniformSphere N) :=
    sphere_cont_integrable hN ((continuous_apply i).pow k)
  have iA := (ip 4).const_mul (angularA N ^ 2)
  have iB := (ip 2).const_mul (2 * angularA N * e)
  have iC := integrable_const (μ := uniformSphere N) (e ^ 2)
  have iD := (ip 6).const_mul (2 * angularA N * angularB N)
  have iE := (ip 8).const_mul (angularB N ^ 2)
  have iAB : Integrable (fun u : Fin N → ℝ => angularA N ^ 2 * u i ^ 4 + 2 * angularA N * e * u i ^ 2) (uniformSphere N) := iA.add iB
  have iABC : Integrable (fun u : Fin N → ℝ => angularA N ^ 2 * u i ^ 4 + 2 * angularA N * e * u i ^ 2 + e ^ 2) (uniformSphere N) := iAB.add iC
  have iABCD : Integrable (fun u : Fin N → ℝ => angularA N ^ 2 * u i ^ 4 + 2 * angularA N * e * u i ^ 2 + e ^ 2 + 2 * angularA N * angularB N * u i ^ 6) (uniformSphere N) := iABC.add iD
  rw [integral_add iABCD iE, integral_add iABC iD, integral_add iAB iC, integral_add iA iB]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [sphere_coordinate_even hN i 2, sphere_coordinate_even hN i 1,
    sphere_coordinate_even hN i 3, sphere_coordinate_even hN i 4]
  rfl

lemma continuous_angularK (N : ℕ) (e : ℝ) : Continuous (angularK N e) :=
  (((continuous_kappa.sub continuous_const).sub (continuous_id.div_const 2)).div_const _).add continuous_const

lemma angular_second_polynomial_integrable {N : ℕ} (hN : 1 ≤ N) (i : Fin N) (e : ℝ) :
    Integrable (fun u : Fin N → ℝ => angularA N ^ 2 * u i ^ 4 + 2 * angularA N * e * u i ^ 2 + e ^ 2 +
      2 * angularA N * angularB N * u i ^ 6 + angularB N ^ 2 * u i ^ 8) (uniformSphere N) := by
  have := uniformSphere_isProbability N hN
  have ip (k : ℕ) : Integrable (fun u : Fin N → ℝ => u i ^ k) (uniformSphere N) :=
    sphere_cont_integrable hN ((continuous_apply i).pow k)
  exact (((((ip 4).const_mul (angularA N ^ 2)).add ((ip 2).const_mul (2 * angularA N * e))).add
    (integrable_const (e ^ 2))).add ((ip 6).const_mul (2 * angularA N * angularB N))).add
    ((ip 8).const_mul (angularB N ^ 2))

lemma angular_second_ae {N : ℕ} (hN : 1 ≤ N) (i : Fin N) {e : ℝ} (he : e ≤ 0) :
    ∀ᵐ u : Fin N → ℝ ∂uniformSphere N, angularK N e (u i) ^ 2 ≤
      angularA N ^ 2 * u i ^ 4 + 2 * angularA N * e * u i ^ 2 + e ^ 2 +
      2 * angularA N * angularB N * u i ^ 6 + angularB N ^ 2 * u i ^ 8 := by
  filter_upwards [uniformSphere_ae_sphere N] with u hu
  exact angularK_square_bound (N := N) (e := e) (x := u i) hN he (sphere_coordinate_abs hu i)

theorem angular_second_moment {N : ℕ} (hN : 1 ≤ N) (i : Fin N) {e : ℝ} (he : e ≤ 0) :
    (∫ u : Fin N → ℝ, angularK N e (u i) ^ 2 ∂uniformSphere N) ≤ angularJ2 N e := by
  rw [← angular_second_polynomial_integral hN i e]
  apply integral_mono_ae
  · exact sphere_cont_integrable hN (((continuous_angularK N e).comp (continuous_apply i)).pow 2)
  · exact angular_second_polynomial_integrable hN i e
  · exact angular_second_ae hN i he

theorem angular_fourth_moment {N : ℕ} (hN : 1 ≤ N) (i : Fin N) (e : ℝ) :
    (∫ u : Fin N → ℝ, angularK N e (u i) ^ 4 ∂uniformSphere N) ≤ angularJ4 N e := by
  have hk := continuous_kappa
  have hc : Continuous (fun x => (angularA N * x ^ 2 + |e| + angularB N * x ^ 4) ^ 4) := by fun_prop
  have hb := integral_mono_ae (sphere_cont_integrable hN (by unfold angularK angularG; fun_prop))
    (sphere_cont_integrable hN (hc.comp (continuous_apply i)))
    (show ∀ᵐ u ∂uniformSphere N, angularK N e (u i) ^ 4 ≤ _ from by
      filter_upwards [uniformSphere_ae_sphere N] with u hu
      exact angularK_four_bound hN (sphere_coordinate_abs hu i))
  simp only [Function.comp_apply] at hb
  refine hb.trans_eq ?_
  have he : ∀ x : ℝ, (angularA N * x ^ 2 + |e| + angularB N * x ^ 4) ^ 4 =
      ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range (5 - j),
        (Nat.choose 4 j : ℝ) * (Nat.choose (4 - j) l : ℝ) * angularA N ^ j * |e| ^ (4 - j - l) *
          angularB N ^ l * x ^ (2 * (j + 2 * l)) := by
    intro x
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring_nf
    simp only [sq_abs]
    <;> ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun l _ =>
    sphere_cont_integrable hN (by fun_prop))]
  unfold angularJ4
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum _ (fun l _ => sphere_cont_integrable hN (by fun_prop))]
  simp_rw [integral_const_mul, sphere_coordinate_even hN i]

end BstLean.Part218
#print axioms BstLean.Part218.angular_second_moment
#print axioms BstLean.Part218.angular_fourth_moment
