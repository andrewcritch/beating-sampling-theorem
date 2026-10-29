import BstLean.Part78Prob
import BstLean.Part78Bridge
import BstLean.Part78BridgeB
import BstLean.Part78Wick
import BstLean.Part78Sphere
import BstLean.Part78Sharp
import BstLean.Part78Poincare
import BstLean.Part78Var
import BstLean.Part59Main
import BstLean.Part59Prog
import BstLean.Part59CostCmp
import BstLean.Part63RadMom
import BstLean.Part52Reduce

/-!
# Part 78: Theorem 4 at `(d_M, d_f) = (2,2)`, uniform `D`, every quadratic `f` with `H ≠ 0`,
for every `n ≥ 45000`

Role: `delegations/statements/p78-spec.md`. Sources: `delegations/answers/omVL-opus-prover.md`,
`delegations/answers/omVL-cx-disprover.md`.

* `part78_meanIds`, `part78_sphere`, `part78_varBound`: the interface statements with their
  constants (`S2 = 501/500`, `cP = 100·1·(1733/1000)`).
* `part78_c1`: `E[(B − g₀)² | u] ≤ (19/20) V̄(u)/n` (`n ≥ 1000`).
* `part78_cV`: `Var(V | u) ≤ 309 V̄(u)²/n` (`n ≥ 1000`).
* `part78_gauss`: the Gaussian-model theorem given the constant column.
* `fail78`, `part78_22`: the coefficient-sphere theorem, `ε = 1/2`, failure `≤ 1/100`, `n ≥ 45000`.
-/

namespace BstLean.Part78

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part53 (aH)
open BstLean.Part59

variable {n : ℕ}

/-! ## The interfaces, with their constants -/

theorem part78_meanIds (n : ℕ) (hn : 1 ≤ n) : MeanIds n := meanIds n hn wickTwoPoint

theorem part78_sphere (n : ℕ) (hn : 1000 ≤ n) : SphereConsts n (501 / 500) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨a, b, c, d, e, -, g⟩ := sphereConsts n hn1
  refine ⟨a, b, c, d, e, ?_, g⟩
  rw [ss2_exact n hn1]
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h2 : 1500 * (n : ℝ) + 7500 ≤ 2 * ((n : ℝ) + 2) ^ 2 := by nlinarith
  have h3 : (3 * (n : ℝ) + 15) / (2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2) ≤ 1 / 500 / (n : ℝ) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hnpos.le]
  have h4 : (501 / 500 : ℝ) / n = 1 / n + 1 / 500 / n := by ring
  rw [h4]; linarith

theorem part78_varBound (n : ℕ) (hn : 1 ≤ n) : VarBound n (100 * 1 * (1733 / 1000)) :=
  varBound n hn 1 3 (1733 / 1000) (by norm_num) (by norm_num) (by norm_num) poincareMv
    (featOp1 n hn) affFourth3 gaussLin wickTwoPoint (part78_meanIds n hn) (regIface n hn)
    (sphereConsts n hn).2.2.2.2.2.2

theorem part78_varBoundW (n : ℕ) (hn : 1000 ≤ n) :
    VarBoundW n (100 * 1 * (1733 / 1000) * (800 / 449)) :=
  varBoundW_of hn (part78_sphere n hn) (by norm_num) (part78_meanIds n (by omega))
    (part78_varBound n (by omega)) (by norm_num)

/-- **`E[(B − g₀)² | u] ≤ c₁ V̄(u)/n` with `c₁ = 19/20`.** -/
theorem part78_c1 (n : ℕ) (hn : 1000 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ W, errG a H W ^ 2 ∂stdGauss (WIdx n) ≤
      19 / 20 * (∫ W, VG a H W ∂stdGauss (WIdx n)) / n := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hS := part78_sphere n hn
  have hM := part78_meanIds n hn1
  refine (err_le hn hS hM a H hH).trans ?_
  apply div_le_div_of_nonneg_right _ hnpos.le
  have := floor_le hn hS (by norm_num) hM a H hH
  unfold Wf at this
  nlinarith [nsq_nonneg a, frobH_nonneg H]

/-- **`Var(V | u) ≤ c_V V̄(u)²/n` with `c_V = 309`.** -/
theorem part78_cV (n : ℕ) (hn : 1000 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ W, (VG a H W - ∫ W', VG a H W' ∂stdGauss (WIdx n)) ^ 2 ∂stdGauss (WIdx n) ≤
      309 / n * (∫ W, VG a H W ∂stdGauss (WIdx n)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hS := part78_sphere n hn
  have hM := part78_meanIds n hn1
  have hfl := floor_le hn hS (by norm_num) hM a H hH
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n)
  refine (part78_varBound n hn1 a H hH).trans ?_
  have hm0 : 0 ≤ m := le_trans (Wf_nonneg a H) hfl
  have hA8 : nsq a + 8 * frobH H ≤ 800 / 449 * m := by
    unfold Wf at hfl; nlinarith [nsq_nonneg a, frobH_nonneg H]
  have h1 : 100 * 1 * (1733 / 1000) / (n : ℝ) * (nsq a + 8 * frobH H) * m ≤
      100 * 1 * (1733 / 1000) / (n : ℝ) * (800 / 449 * m) * m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA8 (by positivity)) hm0
  refine h1.trans ?_
  have h2 : 100 * 1 * (1733 / 1000) / (n : ℝ) * (800 / 449 * m) * m =
      (100 * 1 * (1733 / 1000) * (800 / 449)) / n * m ^ 2 := by ring
  rw [h2]
  have h3 : (100 * 1 * (1733 / 1000) * (800 / 449) : ℝ) / n ≤ 309 / n :=
    div_le_div_of_nonneg_right (by norm_num) hnpos.le
  exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

/-- **The Gaussian-model theorem, given the constant column** (`a = ℓ + 2Hu`), `n ≥ 1000`:
failure `≤ c₁/(n ε² κ) + c_V/(n (1−κ)²)`, `c₁ = 19/20`, `c_V = 173.3·800/449 < 309`, `κ = 1 − θ`. -/
theorem part78_gauss (n : ℕ) (hn : 1000 ≤ n) (κ ε : ℝ) (hκ0 : 0 < κ) (hκ : κ < 1) (hε : 0 < ε)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < frobH H) :
    stdGauss (WIdx n) {W | ε ^ 2 * VG a H W < errG a H W ^ 2} ≤
      ENNReal.ofReal (19 / 20 / (n * (ε ^ 2 * κ)) +
        100 * 1 * (1733 / 1000) * (800 / 449) / (n * (1 - κ) ^ 2)) :=
  gauss_model hn (part78_sphere n hn) (by norm_num) (part78_meanIds n (by omega))
    (part78_varBoundW n hn) (by norm_num) (by norm_num) (by norm_num) hκ0 hκ hε a H hH hpos

/-! ## The radius -/

lemma radius_tail (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    stdGauss (CoefIdxD n 2) {Z | δ ^ 2 < ((∑ α, Z α ^ 2) / DD n 2 - 1) ^ 2} ≤
      ENNReal.ofReal (2 / DD n 2 / δ ^ 2) := by
  have hD : 0 < DD n 2 := BstLean.Part36.DD_pos hn
  have hev : ∀ Z : CoefIdxD n 2 → ℝ,
      MvPolynomial.eval Z (BstLean.Part53.T2Aux.radialPoly n 2 (BstLean.Part53.sg n 2)) =
        (∑ α, Z α ^ 2) / DD n 2 := by
    intro Z
    have hs : (BstLean.Part53.sg n 2) ^ 2 = 1 / DD n 2 := by
      rw [BstLean.Part53.sg, div_pow, one_pow, Real.sq_sqrt hD.le]
    simp only [BstLean.Part53.T2Aux.radialPoly, map_sum, map_pow, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, mul_pow, hs]
    rw [← Finset.mul_sum]; ring
  have hB := BstLean.Part63.centered_exact63 n 2 hn 1 le_rfl (by norm_num)
  simp only [hev, mul_one, pow_one] at hB
  have hB' : ∫ Z, ((∑ α, Z α ^ 2) / DD n 2 - 1) ^ 2 ∂stdGauss (CoefIdxD n 2) ≤ 2 / DD n 2 := by
    simpa [BstLean.Part63.mR63] using hB
  have hgood : Good (stdGauss (CoefIdxD n 2))
      (fun Z : CoefIdxD n 2 → ℝ => ((∑ α, Z α ^ 2) / DD n 2 - 1) ^ 2) := by
    have h1 : Good (stdGauss (CoefIdxD n 2)) (fun Z : CoefIdxD n 2 → ℝ => ∑ α, Z α ^ 2) :=
      Good.sum _ fun α _ => (good_coord α).pow 2
    have h2 := ((h1.mul_const (1 / DD n 2)).sub (Good.const 1)).pow 2
    have h3 : (fun Z : CoefIdxD n 2 → ℝ => ((∑ α, Z α ^ 2) / DD n 2 - 1) ^ 2) =
        fun Z => ((∑ α, Z α ^ 2) * (1 / DD n 2) - 1) ^ 2 := by
      funext Z; ring
    rw [h3]; exact h2
  exact markov_gt (fun Z => sq_nonneg _) hgood.integrable (by positivity) hB'

lemma tau_close {q D δ : ℝ} (hq : 0 < q) (hD : 0 < D) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (h : (q / D - 1) ^ 2 ≤ δ ^ 2) : |Real.sqrt D * (1 / Real.sqrt q) - 1| ≤ δ := by
  obtain ⟨hl, hu⟩ := abs_le_of_sq_le_sq' h hδ0
  set τ := Real.sqrt D * (1 / Real.sqrt q) with hτ
  set w := q / D with hw
  have hτ0 : 0 < τ := by positivity
  have hτw : τ ^ 2 * w = 1 := by
    rw [hτ, hw, mul_pow, div_pow, one_pow, Real.sq_sqrt hD.le, Real.sq_sqrt hq.le]
    field_simp
  have hw0 : 0 < w := by positivity
  rw [abs_le]
  constructor
  · by_contra hc
    rw [not_le] at hc
    have h1 : τ < 1 - δ := by linarith
    have h2 : τ ^ 2 < (1 - δ) ^ 2 := by nlinarith
    nlinarith [mul_pos hτ0 hw0, sq_nonneg δ, mul_nonneg hδ0 (sq_nonneg δ)]
  · by_contra hc
    rw [not_le] at hc
    have h1 : 1 + δ < τ := by linarith
    have h2 : (1 + δ) ^ 2 < τ ^ 2 := by nlinarith
    nlinarith [mul_pos hτ0 hw0, sq_nonneg δ, mul_nonneg hδ0 (sq_nonneg δ)]

/-! ## The split coordinates -/

lemma comb_facts (u : Fin n → ℝ) (W : WIdx n → ℝ) :
    colM (combEquiv n (u, W)) default = u ∧
    (∀ (x : Fin n → ℝ) (i : Fin n), mapMD (combEquiv n (u, W)) x i = u i + zv W (pf x) i) ∧
    ∑ α, combEquiv n (u, W) α ^ 2 = ∑ i, u i ^ 2 + ∑ β, W β ^ 2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact combEquiv_inl u W i
  · intro x i
    rw [BstLean.Part49.mapMD_eq]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (default : Mono n 2))]
    congr 1
    · have h1 : phiM x (default : Mono n 2) = 1 := by
        show BstLean.Part36.monoVal x (Sym.nil : Sym (Fin n) 0).1 = 1
        simp [BstLean.Part36.monoVal]
      rw [h1, mul_one]
      exact combEquiv_inl u W i
    · unfold zv pf
      have hs : (Finset.univ.erase (default : Mono n 2)) =
          Finset.univ.filter (fun q : Mono n 2 => q ≠ default) := by
        ext q; simp
      rw [hs, ← Finset.sum_subtype_eq_sum_filter (p := fun q : Mono n 2 => q ≠ default)]
      apply Finset.sum_congr
      · ext q; simp
      · intro q _
        rw [combEquiv_inr u W q i]
  · rw [← (splitEquiv n).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ i : Fin n, combEquiv n (u, W) (splitEquiv n (Sum.inl i)) = u i :=
      fun i => combEquiv_inl u W i
    have h2 : ∀ β : WIdx n, combEquiv n (u, W) (splitEquiv n (Sum.inr β)) = W β :=
      fun β => combEquiv_inr u W β.1 β.2
    simp only [h1, h2]

/-! ## The coefficient-sphere theorem -/

set_option maxHeartbeats 1600000 in
/-- **Failure probability of `g₀` on the coefficient sphere, parametric form**: `(2,2)`, uniform
`D`, every `n ≥ 1000`, every quadratic `f` with a nonzero degree-two part. The parameters are the
variance constant `cP`, the floor level `κ = 1 − θ`, the Markov level `ε₁`, and `lam`, `t`. -/
theorem fail78_core (n : ℕ) (hn1000 : 1000 ≤ n) {cW κ ε ε₁ lam t : ℝ} (hV : VarBoundW n cW)
    (hcW : 0 ≤ cW) (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (ht : 0 < t)
    (hnumc : 11 / 10 * ε₁ ^ 2 + (229 + ε ^ 2 * t / lam) * (1 / (n : ℝ)) * (100 / 449) ≤
      ε ^ 2 * (1 - lam) * κ)
    (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal ((4 + 19 / 20 / ε₁ ^ 2 + cW / (1 - κ) ^ 2 + 567 / 50 / t +
        1 / 100) * (1 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn1000
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨ℓ₀, H₀, hH₀, hpoly, htop, hg0⟩ := coefBridge n c
  obtain ⟨hDv, haH⟩ := ddval n
  have hD : 0 < DD n 2 := BstLean.Part36.DD_pos hn1
  set D := DD n 2 with hDdef
  set sD := Real.sqrt D with hsDdef
  have hsD0 : 0 < sD := Real.sqrt_pos.mpr hD
  have hsD : sD ^ 2 = D := Real.sq_sqrt hD.le
  set ℓ : Fin n → ℝ := fun i => ℓ₀ i / sD with hℓdef
  set H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => H₀ i j / D with hHdef
  have hH : H.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [hHdef, Matrix.of_apply]
    rw [hH₀.apply j i]
  have hℓ : ∀ i, ℓ₀ i = sD * ℓ i := fun i => by simp only [hℓdef]; field_simp
  have hHs : ∀ i j, H₀ i j = D * H i j := fun i j => by
    simp only [hHdef, Matrix.of_apply]; field_simp
  have hv : 0 < frobH H := by
    have h0 := htop hc
    have : frobH H = frobH H₀ / D ^ 2 := by
      unfold frobH
      simp only [hHdef, Matrix.of_apply, div_pow]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
    rw [this]; positivity
  set δ : ℝ := 1 / n with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ100 : δ ≤ 1 / 100 := by
    rw [hδdef, div_le_div_iff₀ hnpos (by norm_num)]; linarith
  -- the two bad sets
  set UW : Set ((Fin n → ℝ) × (WIdx n → ℝ)) := {p | |sD * sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun (c default) ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun (c default) ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i))
            ∂uniformSphere n) -
          (qfun (c default) ℓ₀ H₀ (fun i => sOf p * p.1 i) + 3 / 2 / D * trH H₀)) ^ 2} with hUW
  have hsub : {Z : CoefIdxD n 2 → ℝ | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ⊆
      {Z | δ ^ 2 < ((∑ α, Z α ^ 2) / D - 1) ^ 2} ∪ (combEquiv n).symm ⁻¹' UW := by
    intro Z hZ
    obtain ⟨hZ0, hfail⟩ := hZ
    by_cases hr : δ ^ 2 < ((∑ α, Z α ^ 2) / D - 1) ^ 2
    · exact Or.inl hr
    right
    simp only [Set.mem_preimage]
    set p := (combEquiv n).symm Z with hp
    have hZp : combEquiv n (p.1, p.2) = Z := by
      show combEquiv n p = Z
      rw [hp]; exact (combEquiv n).apply_symm_apply Z
    obtain ⟨f1, f2, f3⟩ := comb_facts p.1 p.2
    rw [hZp] at f1 f2 f3
    have hq : 0 < ∑ α, Z α ^ 2 := by
      by_contra hc0
      apply hZ0
      have h0 : ∑ α, Z α ^ 2 = 0 :=
        le_antisymm (not_lt.mp hc0) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      funext α
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0 α (Finset.mem_univ α)
      simpa using this
    have hs : sOf p = 1 / Real.sqrt (∑ α, Z α ^ 2) := by unfold sOf; rw [f3]
    have hunit : unitOfD Z = sOf p • Z := by unfold unitOfD; rw [hs]
    have hτ : |sD * sOf p - 1| ≤ δ := by
      rw [hs]
      exact tau_close hq hD hδ0.le (by linarith) (not_lt.mp hr)
    have hmap : ∀ x : Fin n → ℝ, polyEval 2 c (mapMD (sOf p • Z) x) =
        qfun (c default) ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i)) := by
      intro x
      rw [hpoly]
      congr 1
      funext i
      rw [BstLean.Part52.mapMD_smul, f2]
    have hcol : colM (sOf p • Z) default = fun i => sOf p * p.1 i := by
      funext i
      have := congrFun f1 i
      simp only [colM, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this]
    refine ⟨hτ, ?_⟩
    have e1 : varP (uniformSphere n) 2 c (unitOfD Z) = varU (uniformSphere n)
        (fun x => qfun (c default) ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i))) := by
      unfold varP; rw [hunit]; simp only [hmap]
    have e2 : BP (uniformSphere n) 2 c (unitOfD Z) =
        ∫ x, qfun (c default) ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i))
          ∂uniformSphere n := by
      unfold BP; rw [hunit]; simp only [hmap]
    have e3 : g0Q n 2 2 c (unitOfD Z) =
        qfun (c default) ℓ₀ H₀ (fun i => sOf p * p.1 i) + 3 / 2 / D * trH H₀ := by
      rw [hunit, hg0, hcol, haH]
    rw [e1, e2, e3] at hfail
    exact hfail
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hrad := radius_tail n hn1 δ hδ0
  have hpre : stdGauss (CoefIdxD n 2) ((combEquiv n).symm ⁻¹' UW) =
      ((stdGauss (Fin n)).prod (stdGauss (WIdx n))) UW := by
    rw [← combEquiv_preserving.measure_preimage_equiv, ← Set.preimage_comp]
    simp
  have huw := uw_fail hn1000 (S2 := 501 / 500) (cW := cW) (c1 := 19 / 20)
    (κ := κ) (ε := ε) (ε₁ := ε₁) (lam := lam) (TQ := t * n) (T2 := n) (δ := δ)
    (part78_sphere n hn1000) (by norm_num) (by norm_num) (part78_meanIds n hn1)
    hV (regIface n hn1) gaussLin hcW (by norm_num) (by norm_num)
    hκ0 hκ hε₁ hlam0 hlam1 (by positivity) hnpos hδ100
    (by
      have e : (11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * n + 207 * δ ^ 2 * (n : ℝ) +
          ε ^ 2 * δ ^ 2 * (t * n) / lam) * (100 / 449)) =
          11 / 10 * ε₁ ^ 2 + (229 + ε ^ 2 * t / lam) * (1 / (n : ℝ)) * (100 / 449) := by
        rw [hδdef]; field_simp; ring
      rw [e]
      exact hnumc)
    (c default) ℓ₀ ℓ H₀ H hH hv sD D hsD hD.ne' hℓ hHs
  rw [hpre]
  refine (add_le_add hrad huw).trans ?_
  have h1κ : 0 < 1 - κ := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have t1 : 2 / D / δ ^ 2 ≤ 4 * (1 / n) := by
    rw [hDv, hδdef]
    have e : 2 / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) / (1 / (n : ℝ)) ^ 2 =
        4 * (n : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      field_simp <;> ring
    have e' : 4 * (1 / (n : ℝ)) = 4 / (n : ℝ) := by ring
    rw [e, e', div_le_div_iff₀ (by positivity) hnpos]
    nlinarith
  have t2 : (19 / 20 : ℝ) / (n * ε₁ ^ 2) = 19 / 20 / ε₁ ^ 2 * (1 / n) := by
    field_simp
  have t3 : cW / (n * (1 - κ) ^ 2) = cW / (1 - κ) ^ 2 * (1 / n) := by
    field_simp
  have t4 : (151 / 100 * 4 + 53 / 10 : ℝ) / (t * n) = 567 / 50 / t * (1 / n) := by
    field_simp; norm_num
  have t5 : (4 + (2 * (501 / 500) + 9 / 4) : ℝ) / (n * n) ≤ 1 / 100 * (1 / n) := by
    have : (4 + (2 * (501 / 500) + 9 / 4) : ℝ) / (n * n) =
        ((4 + (2 * (501 / 500) + 9 / 4)) * (1 / n)) * (1 / n) := by field_simp
    rw [this]
    have hx : 1 / (n : ℝ) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
    exact mul_le_mul_of_nonneg_right (by nlinarith) hx0.le
  rw [t2, t3, t4]
  linarith

/-- **Failure probability of `g₀` on the coefficient sphere**, `(2,2)`, uniform `D`, `ε = 1/2`,
every `n ≥ 45000`, every quadratic `f` with a nonzero degree-two part. -/
theorem fail78 (n : ℕ) (hn : 45000 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn' : (45000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx : 1 / (n : ℝ) ≤ 1 / 45000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hx' : (n : ℝ)⁻¹ ≤ 1 / 45000 := by rw [← one_div]; exact hx
  refine (fail78_core n (by omega) (cW := 100 * 1 * (1733 / 1000) * (800 / 449)) (κ := 2 / 25) (ε := 1 / 2)
    (ε₁ := 127 / 1000) (lam := 1 / 50) (t := 8) (part78_varBoundW n (by omega)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; linarith) c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num
  linarith

/-- **Theorem 4 at `(d_M, d_f) = (2,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 45000`.** One straight-line program from the constants `0` and `1` reads only the constant
column of `m` and the coefficients of `f`, computes `g₀`, costs less than the charged baseline, and
for every quadratic `f` with a nonzero coefficient of degree two (`TopNZ 2 c`) fails with
probability `≤ 1/100` over `m` uniform on the coefficient sphere. This is the statement of
`Part59.part59_general` at `(2,2)` with `μ = uniformSphere n` and the explicit threshold `45000`. -/
theorem part78_22 :
    ∀ n : ℕ, 45000 ≤ n → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n 2 2 hn1 (by norm_num) (by norm_num)
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 2 (1 / 2) pg.cost hcost
    ((costG59_lt_twoPp n 2 2 (by norm_num) (by omega)).trans_le (twoPp_le_baselineF n 2 2 (1 / 2))),
    ?_⟩
  intro c hc
  have heval : ∀ M : CoefIdxD n 2 → ℝ, pg.eval (inp59 c M) () = g0Q n 2 2 c M := by
    intro M
    rw [hspec, (cv59_inp 2 c M).1, (cv59_inp 2 c M).2]
  simp only [heval]
  exact fail78 n hn c hc

end BstLean.Part78

#print axioms BstLean.Part78.part78_22
#print axioms BstLean.Part78.fail78
#print axioms BstLean.Part78.fail78_core
#print axioms BstLean.Part78.part78_gauss
#print axioms BstLean.Part78.part78_c1
#print axioms BstLean.Part78.part78_cV
#print axioms BstLean.Part78.part78_meanIds
#print axioms BstLean.Part78.part78_varBound
