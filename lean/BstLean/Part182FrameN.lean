import BstLean.Part160Split3

/-!
# Part 182 (file `FrameN`): the frame bound at one retained value with a SEPARATE covariance constant

No proof is left open; no `native_decide` or `axiom` is used.

`frameA_point3N` is Part 160's `frameA_point3` (split of second order) with one change: the main
term uses a covariance constant `Ncov` given by the hypothesis `COV_at D c Ncov` (in Part 160 it is
obtained from `Ξ ≤ N γ_A/n` by `cov_at_of_XiS`, so `Ncov = N`). The constant `N` (a bound of `Ξ`)
is still used in the middle term (the fourth moment and the gap) and in `q`. So a sharper
covariance bound (the paper's Schur certificate, `N_cov ≤ 0.342`) lowers the main term
`(Ncov + ξ)/s²` only. The proof is a copy of `frameA_point3`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157 BstLean.Part160
open BstLean.Part134 (lam res sig eDir eDir_unit_or_zero measurable_eDir measurable_res)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS Xi4 N2 sq2 hid2Mean_cr)

variable {n : ℕ}

theorem frameA_point3N (hn : 10 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) {N Ncov a eb xi e1 e2 N22 q sd s r η κ ρ elo l1 mu cf : ℝ} (hN0 : 0 ≤ N) (hNc0 : 0 ≤ Ncov) (hcov : COV_at D c Ncov)
    (hb : 0 < normSq ((1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (hXi8 : Xi8 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤
        xi * (2 / (n : ℝ)) / n)
    (hN2 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / (n : ℝ) ≤ e2 ^ 2)
    (hq : 2 * N / n ≤ q)
    (hsd : 0 < sd) (hs : sd < s) (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - q)
    (ha0 : 0 ≤ a) (hr : 0 ≤ r) (hr2 : 4 * a ^ 2 + N ^ 2 ≤ r ^ 2) (hη : 0 < η) (hκ0 : 0 < κ)
    (hκ : (1 + η) ^ 3 * (2 * a + r) ^ 2 + (1 + 1 / η) ^ 3 * xi ^ 2 ≤ κ ^ 2)
    (hρ0 : 0 < ρ) (hρ : N / n ≤ ρ ^ 2)
    (hlo : 2 / (n : ℝ) * elo ≤ 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c))) (hl1 : l1 ^ 2 ≤ elo) (hl12 : e2 ≤ l1)
    (hmu0 : 0 < mu) (hmu : (1 + N22) ^ 2 - (l1 - e2) ^ 2 ≤ mu ^ 2)
    (hsum : (Ncov + xi) / s ^ 2 + 2 * κ * mu * ρ / (sd ^ 2 * s ^ 2) +
      (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) ≤ cf)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs0 : 0 < s := lt_trans hsd hs
  have hgap : 0 < s - sd := by linarith
  have hN2nn := BstLean.Part153.N2_nonneg 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN2
  have hs2' : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n := by linarith
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, w j ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← hS]
  by_cases hSz : S = 0
  · have hw : w = 0 := BstLean.Part134.eq_zero_of_normSq (by rw [← hSz, hS]; rfl)
    simp [hw, hSz]
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSz)
  have hcen : CENTRE_at D c xi := by
    unfold CENTRE_at
    rw [hD c, muStand_eq]
    exact hxi
  have hT1 := Cr_at hn1 D c hNc0 hcov hcen w
  rw [← hS] at hT1
  rw [← hD c] at hb heb hxi hlo
  obtain ⟨b, hbd⟩ : ∃ b : Fin (mA n) → ℝ, b = D.bA c.1 c.2.1.1 := ⟨_, rfl⟩
  rw [← hbd] at hb heb hxi hlo hT1 ⊢
  have hint : Integrable (fun ξ => (∑ j, res b (hStand D c ξ) j * w j) ^ 2) (stdGauss (Fin n)) := by
    simp_rw [res_symm b _ w]
    exact hStand_int2 hn1 D c (res b w)
  obtain ⟨hint4, hP4⟩ := resid_fourth hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ b w hXi hXi4 hxi ha0 hr
    hr2 hη hκ0.le hκ
  rw [← hS] at hP4
  have hQ2 := gap_sq' hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi heb hxi hN2 he1 he1' he2 he2' hs2'
    hρ hlo hl1 hl12 hmu0.le hmu
  have hm8 := mass_bound8 hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi hXi4 hXi8 heb hxi hN2 he1 he1'
    he2 he2' hsd.le hs hs2'
  -- the cutoffs
  obtain ⟨ac, hac⟩ : ∃ ac : ℝ, ac = 2 / (n : ℝ) * sd ^ 2 / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Ac, hAc⟩ : ∃ Ac : ℝ, Ac = 2 / (n : ℝ) * s ^ 2 / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hac0 : 0 < ac := by rw [hac]; positivity
  have hAc0 : 0 < Ac := by rw [hAc]; positivity
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = κ * (2 / (n : ℝ) / n) * S / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = 2 * (2 / (n : ℝ)) * mu * ρ / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hPd]; positivity
  have hQ0 : 0 < Q := by rw [hQd]; positivity
  rw [← hPd] at hP4
  rw [← hAc, ← hQd] at hQ2
  have h1 := frame_split2 (stdGauss (Fin n)) (BstLean.Part160.measurable_hStand D c) b w hac0 hAc0 hP0 hQ0 hint
    hint4 hP4 hQ2
  rw [← hS] at h1
  have hset : {ξ : Fin n → ℝ | normSq (res b (hStand D c ξ)) < ac} =
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 c.2.1.1.1 c.2.1.1.2
        (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    change normSq (res b (hStand D c ξ)) < ac ↔
      2 / (mA n : ℝ) * normSq (res b (hStand D c ξ)) < 2 / (n : ℝ) * sd ^ 2
    rw [hac, lt_div_iff₀ (by positivity), mul_comm]
  rw [hset] at h1
  obtain ⟨Pm, hPm⟩ : ∃ Pm : ℝ, Pm = (stdGauss (Fin n)).real
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 c.2.1.1.1 c.2.1.1.2
        (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := ⟨_, rfl⟩
  rw [← hPm] at h1 hm8
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ ξ, (∑ j, res b (hStand D c ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hI] at h1 hT1
  obtain ⟨M8, hM8⟩ : ∃ M8 : ℝ, M8 = (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) :=
    ⟨_, rfl⟩
  rw [← hM8] at hm8 hsum
  -- the three terms
  have t1 : 1 / Ac * I ≤ (Ncov + xi) / s ^ 2 / n * S := by
    have e : 1 / Ac * I = (2 / (mA n : ℝ) * I) / (2 / (n : ℝ) * s ^ 2) := by
      rw [hAc]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (Ncov + xi) / s ^ 2 / n * S * (2 / (n : ℝ) * s ^ 2) =
        (Ncov + xi) * (2 / (n : ℝ)) / n * S := by field_simp
    rw [e2]; exact hT1
  have t2 : P * Q / (ac * Ac) = 2 * κ * mu * ρ / (sd ^ 2 * s ^ 2) / n * S := by
    rw [hPd, hQd, hac, hAc]
    field_simp
  have t3 : Pm * S ≤ M8 / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0
    rw [le_div_iff₀ hnR]; linarith
  have t4 : ((Ncov + xi) / s ^ 2 / n + 2 * κ * mu * ρ / (sd ^ 2 * s ^ 2) / n + M8 / n) * S ≤
      cf / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hsum hnR.le
  rw [t2] at h1
  linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms frameA_point3N
