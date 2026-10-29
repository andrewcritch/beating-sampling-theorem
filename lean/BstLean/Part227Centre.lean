import BstLean.Part227Window

/-! Part 227: centre distance and scalar fluctuation under the uniform World input. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part137 BstLean.Part140 BstLean.Part157 BstLean.Part159

noncomputable def centreDistance (n : ℕ) (Xc : ℝ) : ℝ :=
  (√(Xc / 2) + √((n : ℝ) * perturbation n)) ^ 2

noncomputable def centreFluctuation (n : ℕ) (dT : ℝ) : ℝ :=
  (√dT + √(2 * (n : ℝ) * perturbation n)) ^ 2

noncomputable def centreLower (n : ℕ) (eB : ℝ) : ℝ :=
  (√(kap1 (2 * n) - eB) - √(perturbation n)) ^ 2

/-- The distance to the exact mean retains its exact square-root formula. -/
theorem mean_distance {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n} {Xc : ℝ}
    (hD : θ ∈ goodDist n Xc) (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n) :
    normSq (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) - bWp θ) ≤
      (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * (centreDistance n Xc / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  let S : ℝ := (mW n : ℝ) / ((2 * n : ℕ) : ℝ)
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hD' : normSq (hbarW θ - bhat θ) ≤ S * (Xc / (2 * (n : ℝ))) := by
    change 2 / (mW n : ℝ) * normSq (bhat θ - hbarW θ) ≤
      2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) at hD
    rw [normSq_sub_comm] at hD
    have h := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have he1 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (hbarW θ - bhat θ)) =
        normSq (hbarW θ - bhat θ) := by field_simp
    have he2 : (mW n : ℝ) / 2 * (2 / ((2 * n : ℕ) : ℝ) *
        (Xc / ((2 * n : ℕ) : ℝ))) = S * (Xc / (2 * (n : ℝ))) := by
      dsimp [S]
      push_cast
      field_simp
    rwa [he1, he2] at h
  have hd := BstLean.Part204.bWp_dist hn (BstLean.Part201.constC hn) hS hA
  have hδ : normSq (bWp θ - bhat θ) ≤ S * perturbation n := by
    have h := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have he1 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bWp θ - bhat θ)) =
        normSq (bWp θ - bhat θ) := by field_simp
    have he2 : (mW n : ℝ) / 2 * (2 / ((2 * n : ℕ) : ℝ) *
        (645 / 10 ^ 4 / (mW n : ℝ))) = S * perturbation n := by
      dsimp [S, perturbation]
      ring
    rwa [he1, he2] at h
  have ht : 0 ≤ (n : ℝ) / S := by positivity
  have h1 : (n : ℝ) / S * normSq (hbarW θ - bhat θ) ≤ Xc / 2 := by
    have h := mul_le_mul_of_nonneg_left hD' ht
    have he : (n : ℝ) / S * (S * (Xc / (2 * (n : ℝ)))) = Xc / 2 := by field_simp
    rwa [he] at h
  have h2 : (n : ℝ) / S * normSq (bhat θ - bWp θ) ≤ (n : ℝ) * perturbation n := by
    rw [normSq_sub_comm]
    have h := mul_le_mul_of_nonneg_left hδ ht
    have he : (n : ℝ) / S * (S * perturbation n) = (n : ℝ) * perturbation n := by field_simp
    rwa [he] at h
  have h := BstLean.Part204.normSq_triangle_scaled (hbarW θ - bhat θ)
    (bhat θ - bWp θ) ht h1 h2
  have he : (hbarW θ - bhat θ) + (bhat θ - bWp θ) = hbarW θ - bWp θ := by abel
  rw [he] at h
  change (n : ℝ) / S * normSq (hbarW θ - bWp θ) ≤ centreDistance n Xc at h
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ S / (n : ℝ) by positivity)
  have he' : S / (n : ℝ) * ((n : ℝ) / S * normSq (hbarW θ - bWp θ)) =
      normSq (hbarW θ - bWp θ) := by field_simp
  rw [he'] at h'
  exact h'.trans_eq (by dsimp [S]; ring)

/-- The scalar fluctuation uses the same uniform input in both summands. -/
theorem scalar_fluctuation {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n} {dT : ℝ}
    (hdT : 0 ≤ dT) (hT : θ ∈ goodT n dT) (hH : θ ∈ good136 n)
    (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n) :
    (∫ u, (∑ j, hid2 θ.1 θ.2 u j * bWp θ j -
      (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 ∂uniformSphere (2 * n)) ≤
      ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 *
        (centreFluctuation n dT / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  let S : ℝ := (mW n : ℝ) / ((2 * n : ℕ) : ℝ)
  let δ := bWp θ - bhat θ
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hδ : normSq δ ≤ S * perturbation n := by
    have hd := BstLean.Part204.bWp_dist hn (BstLean.Part201.constC hn) hS hA
    have h := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have he1 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq δ) = normSq δ := by field_simp
    have he2 : (mW n : ℝ) / 2 * (2 / ((2 * n : ℕ) : ℝ) *
        (645 / 10 ^ 4 / (mW n : ℝ))) = S * perturbation n := by
      dsimp [S, perturbation]; ring
    change (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq δ) ≤ _ at h
    rwa [he1, he2] at h
  let f := fun u : Fin (2 * n) → ℝ => ∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S * kap1 (2 * n)
  let g := fun u : Fin (2 * n) → ℝ => ∑ j, hid2 θ.1 θ.2 u j * δ j
  have mf : Continuous f :=
    (continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp (continuous_hid2 θ.1 θ.2)).mul continuous_const).sub continuous_const
  have mg : Continuous g := continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp (continuous_hid2 θ.1 θ.2)).mul continuous_const
  have ms : Continuous (fun u => normSq (hid2 θ.1 θ.2 u)) :=
    continuous_normSq.comp (continuous_hid2 θ.1 θ.2)
  have hscale : (S / √(n : ℝ)) ^ 2 = S ^ 2 / (n : ℝ) := by
    rw [div_pow, Real.sq_sqrt hnpos.le]
  have hf : L2le (uniformSphere (2 * n)) f (S / √(n : ℝ) * √dT) := by
    refine ⟨mf.measurable.aestronglyMeasurable, sphere_cont_integrable hN (mf.pow 2), ?_⟩
    have he : ∀ u, f u ^ 2 = ((mW n : ℝ) / 2) ^ 2 *
        (That (2 * n) (mW n) u θ - 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 := by
      intro u
      dsimp [f, S, That, dotp]
      field_simp
    simp_rw [he]
    rw [integral_const_mul]
    change ((mW n : ℝ) / 2) ^ 2 * errT θ ≤ _
    have ht : errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      have hT' : (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT := hT
      simpa only [mul_comm] using hT'
    refine (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq ?_
    rw [mul_pow, hscale, Real.sq_sqrt hdT]
    dsimp [S]
    ring
  have hpe : 0 ≤ 2 * (n : ℝ) * perturbation n := by unfold perturbation; positivity
  have hg : L2le (uniformSphere (2 * n)) g
      (S / √(n : ℝ) * √(2 * (n : ℝ) * perturbation n)) := by
    refine L2le.of_sq_le mg.measurable.aestronglyMeasurable
      ((sphere_cont_integrable hN ms).const_mul (normSq δ)) ?_ ?_
    · intro u
      have h := dotL_sq_le (hid2 θ.1 θ.2 u) δ
      simpa only [g, mul_comm] using h
    · rw [integral_const_mul]
      have henergy : (∫ u, normSq (hid2 θ.1 θ.2 u) ∂uniformSphere (2 * n)) ≤ 2 * S :=
        sphere_energy_le hn hH
      have h := mul_le_mul hδ henergy
        (integral_nonneg fun u => normSq_nonneg _)
        (by dsimp [perturbation]; positivity)
      refine h.trans_eq ?_
      rw [mul_pow, hscale, Real.sq_sqrt hpe]
      field_simp
      <;> ring
  have he : ∀ u, f u + g u =
      ∑ j, hid2 θ.1 θ.2 u j * bWp θ j - S * kap1 (2 * n) := by
    intro u
    dsimp [f, g, δ]
    have he' : (∑ j, hid2 θ.1 θ.2 u j * bhat θ j) +
        (∑ j, hid2 θ.1 θ.2 u j * (bWp θ - bhat θ) j) =
        ∑ j, hid2 θ.1 θ.2 u j * bWp θ j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
    simp only [Pi.sub_apply] at he'
    linarith only [he']
  have h := ((hf.add' hg (by positivity) (by positivity)).congr_fun he).le
  refine h.trans_eq ?_
  dsimp [centreFluctuation]
  rw [← mul_add, mul_pow, hscale]
  ring

end BstLean.Part227
#print axioms BstLean.Part227.mean_distance
#print axioms BstLean.Part227.scalar_fluctuation
