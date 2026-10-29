import BstLean.Part132All
import BstLean.Part133Top
import BstLean.Part133WorldR
import BstLean.Part133ReluR
import BstLean.Part133CosB

/-!
# Part 133: the variance of `J` at the Focus, and Theorem C

Role: `delegations/statements/p133-spec.md`, items 3 (totals), 4 and 5. Paper source:
`onW4c-cx.md` §4 ("Totals"), §7.

* `vTot`: the total `3·e_P + 2·e_× + e_V` of the Lean chain, for all widths; `varJ_general`:
  `Var J ≤ ((4/n)·vTot)²`.
* `vTot_bound`: `vTot ≤ 3011/10000` at the widths of the Focus, `r = 2`, every `n ≥ 4 096`.
* **`varJ133`**: `Var J ≤ (23/25)·((314/1000)·(4/n))²` for every `n ≥ 4 096`.
* **`thmC133`**: Theorem C with no hypothesis. **`sep133`**: the separation probability `≥ 1/16`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

/-! ## The constants of the chain -/

/-- The second-order term of the cosine link (the last matrix of `W` and the normalization). -/
noncomputable def jCos (n : ℕ) : ℝ := 15 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ)

/-- The link of the inputs: `‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ sU N`. -/
noncomputable def sU (N : ℕ) : ℝ := 507 / 1000 / √(N : ℝ) + 8 / 25 * √3 / (N : ℝ)

/-- The links `F`, `A_3`, `A_2`, `A_1` of the same-`A` kernel. -/
noncomputable def eAFr (n mA mF : ℕ) : ℝ :=
  cF2o mF * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))) + cAr (kappa ∘ kappa) mA n

/-- The relative deficit of `E|A(x)|` below `√2`. -/
noncomputable def dA (n mA : ℕ) : ℝ := dChi n + epsW mA / 2

/-- The cross kernel. -/
noncomputable def eXr (n mA mF : ℕ) : ℝ :=
  cF2o mF + 1 / √(n : ℝ) + kappa (kappa 0) * (2 * √(dA n mA))

/-- The small terms of the World link. -/
noncomputable def eWsmall (n mW : ℕ) : ℝ :=
  jCos n + (1 + 2 / √(n : ℝ)) * eHid mW + 2 * √(epsW mW)

/-- The World link, after the average over the inputs. -/
noncomputable def eWr (N n mW : ℕ) : ℝ :=
  1 / √(n : ℝ) * (1 - kappa (kappa 0) ^ 2 + 2 * sU N) + eWsmall n mW

/-- **The total** `3·e_P + 2·e_× + e_V`, `e_P = eAFr + eWr + sU`. -/
noncomputable def vTot (N mW n mA mF : ℕ) : ℝ :=
  3 * (eAFr n mA mF + eWr N n mW + sU N) + 2 * eXr n mA mF + eV n mA mF

lemma q_mem : 0 ≤ kappa (kappa 0) ∧ kappa (kappa 0) ≤ 1 :=
  ⟨kappa2_zero_pos.le, by linarith [kappa2_zero_le]⟩

section General

variable {N mW n mA mF : ℕ}

lemma cF2o_pos (hmF : 1 ≤ mF) : 0 < cF2o mF := by
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  unfold cF2o
  positivity

lemma cAr_pos {G : ℝ → ℝ} (hG : KGood G) {m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) :
    0 < cAr G m q := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hK := K4_nonneg q
  unfold cAr
  positivity

lemma dChi_nonneg (m : ℕ) : 0 ≤ dChi m := by
  have hK := K4_nonneg m
  unfold dChi
  positivity

lemma eHid_nonneg (m : ℕ) : 0 ≤ eHid m := by
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  unfold eHid
  positivity

lemma sU_nonneg (N : ℕ) : 0 ≤ sU N := by unfold sU; positivity

lemma eWsmall_nonneg (n mW : ℕ) : 0 ≤ eWsmall n mW := by
  have := eHid_nonneg mW
  unfold eWsmall jCos
  positivity

/-! ## The three kernels and the variance of `J`, all widths -/

/-- **The totals of the `L²` chain, for all widths** (`S = 4/n`, under `(u, u′) ⊗ (W, A, A′, F)`):
`‖k_{A,A}(x(u), x(u′)) − S·κ^{∘6}(0)‖₂ ≤ S·(eAFr + eWr + sU)`,
`‖k_{A,A′}(x(u), x(u′)) − S·κ(κ(0))‖₂ ≤ S·eXr`, `‖k_{A,A}(x(u), x(u)) − S‖₂ ≤ S·eV`. -/
theorem kernels_general (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (hd : dChi n ≤ 1) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - 4 / (n : ℝ) * kappa^[6] 0)
      (4 / (n : ℝ) * (eAFr n mA mF + eWr N n mW + sU N)) ∧
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false true false ω - 4 / (n : ℝ) * kappa (kappa 0)) (4 / (n : ℝ) * eXr n mA mF) ∧
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false true ω - 4 / (n : ℝ)) (4 / (n : ℝ) * eV n mA mF) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmW' : (0 : ℝ) < mW := by exact_mod_cast hmW
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hG0 : 3 / 10 ≤ (kappa ∘ kappa) 0 := by
    have := kappa2_zero_ge
    simp only [Function.comp_apply]
    linarith
  have hcF := cF2o_pos hmF
  have hcA := cAr_pos hG hmA hn
  have hdC := dChi_nonneg n
  have hε := epsW_nonneg mA
  have hεpos : 0 < dA n mA := by
    have : 0 < dChi n := by
      have hK := K4_nonneg n
      unfold dChi
      positivity
    unfold dA
    linarith
  have hq := q_mem
  have hsU := sU_nonneg N
  have hsm := eWsmall_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have := lawU2_prob hN
  -- same-`A` kernel
  have hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x'))
        (4 / (n : ℝ) * eAFr n mA mF) := fun x x' hx hx' =>
    kern_same_L2_of hn hmA hx hx' hcF hcA (fun y y' => KF_L2o hn hmF y y')
      (mlp_psi_L2r hG hG0 hmA hn hn x x')
  -- cross kernel
  have hl : ∀ z : Fin n → ℝ, normSq z = 1 →
      √2 * (1 - dA n mA) ≤ ∫ a : MlpParam n mA n, nrm (mlpEval a z) ∂mlpGauss n mA n := by
    intro z hz
    have h := mlp_nrm_mean_lower (q := n) hmA hn hn hd z
    have e2 : 2 * (n : ℝ) / n = 2 := by field_simp
    rw [e2, nrm_of_normSq_one hz, mul_one] at h
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)) h
    unfold dA
    nlinarith [mul_nonneg hdC hε]
  have hX : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.2.1 x x' - 4 / (n : ℝ) * kappa (kappa 0))
        (4 / (n : ℝ) * eXr n mA mF) := fun x x' hx hx' =>
    kern_cross_L2_of hn hmA hx hx' hcF hεpos (fun y y' => KF_L2o hn hmF y y') hl
  -- the World network
  have hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ((fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp v v')) := by
    intro v v' hv hv'
    have hJ : 0 ≤ jCos n := by unfold jCos; positivity
    have h := world_cos_L2g hN hmW hn hJ (fun h h' hh hh' =>
      lin_cos_L2b (v := 2 / (mW : ℝ)) (by positivity) hn h h' hh hh') hv hv'
    refine h.congr_bound ?_
    unfold eWsmall
    ring
  have hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp uu.1 uu.2))
      (eWr N n mW) := by
    have h1 := sphere_gW_L2 hN (1 / √(n : ℝ)) (by positivity)
    have h2 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => eWsmall n mW)
        (eWsmall n mW) := ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    have h3 := h1.add0 h2 (by unfold sU at hsU; positivity) hsm
    exact h3
  have hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU N) := sphere_kk_L2r hN
  have hA0 : 0 ≤ eAFr n mA mF := by unfold eAFr; positivity
  have hX0 : 0 ≤ eXr n mA mF := by
    unfold eXr
    have := hq.1
    positivity
  have hW0 : 0 ≤ eWr N n mW := by unfold eWr; positivity
  exact ⟨kernSame_L2 (mW := mW)
      (gW := fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW)
      hn hN hA0 hW0 hsU hS hW hgW hU,
    kernCross_L2 (N := N) (mW := mW) hn hN hX, kernDiag_L2 (N := N) (mW := mW) hn hN hmA hmF⟩

lemma vTot_nonneg (N mW n mA mF : ℕ) (hmF : 1 ≤ mF) (hmA : 1 ≤ mA) (hn : 1 ≤ n) :
    0 ≤ eAFr n mA mF + eWr N n mW + sU N ∧ 0 ≤ eXr n mA mF ∧ 0 ≤ eV n mA mF ∧
      0 ≤ vTot N mW n mA mF := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcF := cF2o_pos hmF
  have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn
  have hq := q_mem
  have hsU := sU_nonneg N
  have hsm := eWsmall_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hV : 0 ≤ eV n mA mF := Real.sqrt_nonneg _
  have hA0 : 0 ≤ eAFr n mA mF := by unfold eAFr; positivity
  have hX0 : 0 ≤ eXr n mA mF := by
    unfold eXr
    have := hq.1
    positivity
  have hW0 : 0 ≤ eWr N n mW := by unfold eWr; positivity
  refine ⟨by positivity, hX0, hV, ?_⟩
  unfold vTot
  positivity

/-- **The variance of `J` for all widths**: `Var J ≤ ((4/n)·vTot)²`. -/
theorem varJ_general (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (hd : dChi n ≤ 1) :
    Var[Jall; lawAll N mW n mA mF] ≤ (4 / (n : ℝ) * vTot N mW n mA mF) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2, h3⟩ := kernels_general (N := N) (mW := mW) hn hN hmW hmA hmF hd
  obtain ⟨p1, p2, p3, _⟩ := vTot_nonneg N mW n mA mF hmF hmA hn
  have hJ := J_L2 hn hN (by positivity) (by positivity) (by positivity) h1 h2 h3
  refine (variance_le_of_L2le hJ).trans (le_of_eq ?_)
  unfold vTot
  ring

/-- **Item 2 for the five kernels of `J`, all widths**: `Var(P) ≤ Var(k)` for
`P = E_{u,u′}[k | W, A, A′, F]`, with `k` the same-`A` kernel (at `A` and at `A′`), the cross
kernel, and the diagonal kernel (at `A` and at `A′`). -/
theorem var_P_le_var_k (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (hd : dChi n ≤ 1) (pa pa' dg : Bool)
    (hk : (pa, pa', dg) = (false, false, false) ∨ (pa, pa', dg) = (true, true, false) ∨
      (pa, pa', dg) = (false, true, false) ∨ (pa, pa', dg) = (false, false, true) ∨
      (pa, pa', dg) = (true, true, true)) :
    Var[fun r : Rest N mW n mA mF => ∫ uu, kgen pa pa' dg (uu, r) ∂lawU2 N;
        lawR N mW n mA mF] ≤
      Var[kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg;
        (lawU2 N).prod (lawR N mW n mA mF)] := by
  have := lawU2_prob hN
  obtain ⟨h1, h2, h3⟩ := kernels_general (N := N) (mW := mW) hn hN hmW hmA hmF hd
  refine var_section_le hn hN pa pa' dg ?_
  rcases hk with h | h | h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj |> fun ⟨a, b, c⟩ => (⟨a, b, c⟩ : _ ∧ _ ∧ _)
  · exact memLp_of_L2le_sub h1
  · exact memLp_of_L2le_sub (swap_L2 hN false h1)
  · exact memLp_of_L2le_sub h2
  · exact memLp_of_L2le_sub h3
  · exact memLp_of_L2le_sub (swap_L2 hN true h3)

end General

/-! ## The numbers at the Focus, `n ≥ 4 096` -/

lemma sqrt_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  Real.sqrt_le_iff.mpr ⟨hy, h⟩

lemma sqrt2_le : √(2 : ℝ) ≤ 141422 / 100000 := sqrt_le_of_sq (by norm_num) (by norm_num)
lemma sqrt3_le : √(3 : ℝ) ≤ 17321 / 10000 := sqrt_le_of_sq (by norm_num) (by norm_num)
lemma sqrt6_le : √(6 : ℝ) ≤ 24495 / 10000 := sqrt_le_of_sq (by norm_num) (by norm_num)

lemma nR_ge {n : ℕ} (hn : 4096 ≤ n) : (4096 : ℝ) ≤ n := by exact_mod_cast hn

lemma mF_geR {n : ℕ} (hn : 4096 ≤ n) : (262144 : ℝ) ≤ mF n := by exact_mod_cast mF_ge hn

lemma mW_geR {n : ℕ} (hn : 4096 ≤ n) : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge hn

lemma mA_eqR (n : ℕ) : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring

lemma sqrt_mA (n : ℕ) : √(mA n : ℝ) = n := by
  rw [mA_eqR, Real.sqrt_sq (Nat.cast_nonneg n)]

lemma sqrt_mW_ge {n : ℕ} (hn : 4096 ≤ n) : (2097152 : ℝ) ≤ √(mW n : ℝ) := by
  have h := mW_geR hn
  have : √(4398046511104 : ℝ) = 2097152 := by
    rw [show (4398046511104 : ℝ) = 2097152 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← this]
  exact Real.sqrt_le_sqrt h

lemma inv_mA_le {n : ℕ} (hn : 4096 ≤ n) : 5 / (mA n : ℝ) ≤ 3 / 10000000 := by
  have hx := nR_ge hn
  rw [mA_eqR, div_le_iff₀ (by positivity)]
  nlinarith

lemma K4_le {n : ℕ} (hn : 4096 ≤ n) : K4 n ≤ 3466 / 1000 := by
  have hx := nR_ge hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

lemma cF2o_bound {n : ℕ} (hn : 4096 ≤ n) : cF2o (mF n) ≤ 923 / 100000 := by
  have hm := mF_geR hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hc : (5 * kappa 0 + √6) ^ 2 ≤ 16331 / 1000 := by
    have h1 : 5 * kappa 0 + √6 ≤ 40411 / 10000 := by linarith
    have h0 : 0 ≤ 5 * kappa 0 + √6 := by positivity
    nlinarith
  have h5 : 5 / (mF n : ℝ) ≤ 5 / 262144 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  unfold cF2o
  refine sqrt_le_of_sq (by norm_num) ?_
  have e : 6 * (1 + 5 / (mF n : ℝ)) / (mF n : ℝ) + (5 * kappa 0 + √6) ^ 2 / (mF n : ℝ) =
      (6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (mF n : ℝ) := by ring
  rw [e, div_le_iff₀ hm0]
  have h7 : 6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2 ≤ 22332 / 1000 := by
    norm_num at h5 ⊢
    linarith
  nlinarith

lemma sqrt_one_add_le {n : ℕ} (hn : 4096 ≤ n) : √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 4096 := by
  have hx := nR_ge hn
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 2 / (n : ℝ) ≤ 2 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

lemma cAr_bound {n : ℕ} (hn : 4096 ≤ n) : cAr (kappa ∘ kappa) (mA n) n ≤ 3040 / 100000 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hK := K4_le hn
  have hK0 := K4_nonneg n
  have hq := kappa2_zero_le
  have hq0 := q_mem.1
  have h2 := sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have h6 := sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hA := inv_mA_le hn
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hsA : √(1 + 5 / (mA n : ℝ)) ≤ 1 + 1 / 1000000 :=
    sqrt_le_of_sq (by norm_num) (by nlinarith)
  have hsA0 := Real.sqrt_nonneg (1 + 5 / (mA n : ℝ))
  have t1 : (1 + √2 * kappa (kappa 0)) / √(n : ℝ) ≤ (1 + 141422 / 100000 * (49376 / 100000)) / 64 := by
    gcongr
  have t2 : 2 * K4 n * kappa (kappa 0) / (n : ℝ) ≤
      2 * (3466 / 1000) * (49376 / 100000) / 4096 := by
    gcongr
  have t3 : (5 * kappa (kappa 0) + √6) / (n : ℝ) ≤ (5 * (49376 / 100000) + 24495 / 10000) / 4096 := by
    gcongr
  have t4 : (5 + √6) / (n : ℝ) ≤ (5 + 24495 / 10000) / 4096 := by
    gcongr
  have t10 : 0 ≤ (1 + √2 * kappa (kappa 0)) / √(n : ℝ) := by positivity
  have t20 : 0 ≤ 2 * K4 n * kappa (kappa 0) / (n : ℝ) := by positivity
  have t30 : 0 ≤ (5 * kappa (kappa 0) + √6) / (n : ℝ) := by positivity
  unfold cAr
  simp only [Function.comp_apply]
  rw [sqrt_mA]
  have e1 : ((1 + √2 * kappa (kappa 0)) / √(n : ℝ) + 2 * K4 n * kappa (kappa 0) / (n : ℝ)) *
      (1 + 5 / (mA n : ℝ)) ≤
      ((1 + 141422 / 100000 * (49376 / 100000)) / 64 +
        2 * (3466 / 1000) * (49376 / 100000) / 4096) * (1 + 3 / 10000000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have e2 : (5 * kappa (kappa 0) + √6) / (n : ℝ) * √(1 + 5 / (mA n : ℝ)) ≤
      (5 * (49376 / 100000) + 24495 / 10000) / 4096 * (1 + 1 / 1000000) :=
    mul_le_mul t3 hsA hsA0 (by norm_num)
  norm_num at e1 e2 t4 ⊢
  linarith

lemma eAFr_bound {n : ℕ} (hn : 4096 ≤ n) : eAFr n (mA n) (mF n) ≤ 3964 / 100000 := by
  have h1 := cF2o_bound hn
  have h10 : 0 ≤ cF2o (mF n) := Real.sqrt_nonneg _
  have h2 := sqrt_one_add_le hn
  have h20 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
  have h3 := cAr_bound hn
  have hA := inv_mA_le hn
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have e1 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ (1 + 3 / 10000000) * (1 + 1 / 4096) :=
    mul_le_mul (by linarith) h2 h20 (by norm_num)
  have e2 : cF2o (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) ≤
      923 / 100000 * ((1 + 3 / 10000000) * (1 + 1 / 4096)) :=
    mul_le_mul h1 e1 (by positivity) (by norm_num)
  unfold eAFr
  norm_num at e2 ⊢
  linarith

lemma sU_bound {n : ℕ} (hn : 4096 ≤ n) : sU (2 * n) ≤ 568 / 100000 := by
  have hx := nR_ge hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hN : (8192 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hs : (905 / 10 : ℝ) ≤ √(2 * (n : ℝ)) := by
    rw [show (905 / 10 : ℝ) = √((905 / 10) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have h3 := sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  have t1 : 507 / 1000 / √(2 * (n : ℝ)) ≤ 507 / 1000 / (905 / 10) := by gcongr
  have t2 : 8 / 25 * √3 / (2 * (n : ℝ)) ≤ 8 / 25 * (17321 / 10000) / 8192 := by gcongr
  norm_num at t1 t2 ⊢
  linarith

lemma epsW_mW_le {n : ℕ} (hn : 4096 ≤ n) : epsW (mW n) ≤ 25 / 10000000000000 := by
  have hm := mW_geR hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have h5 : 5 / (mW n : ℝ) ≤ 5 / 4398046511104 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have h50 : (0 : ℝ) ≤ 5 / (mW n : ℝ) := by positivity
  unfold epsW
  nlinarith

lemma eWsmall_bound {n : ℕ} (hn : 4096 ≤ n) : eWsmall n (mW n) ≤ 637 / 100000 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hK : √(12 + 48 / (n : ℝ)) ≤ 3466 / 1000 := K4_le hn
  have hK0 := Real.sqrt_nonneg (12 + 48 / (n : ℝ))
  have hε := epsW_mW_le hn
  have hε0 := epsW_nonneg (mW n)
  have hsW := sqrt_mW_ge hn
  have hm := mW_geR hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have s1 : √(5 * epsW (mW n)) ≤ 4 / 1000000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s2 : √(epsW (mW n)) ≤ 2 / 1000000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have t1 : 15 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ) ≤ 15 / 2 * (3466 / 1000) / 4096 := by
    gcongr
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) / 2097152 := by
    gcongr
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤ (5 * (31831 / 100000) + 24495 / 10000) / 2097152 := by
    gcongr
  have t2' : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤ 12 / 10000000 :=
    t2.trans (by norm_num)
  have t3' : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤ 2 / 1000000 := t3.trans (by norm_num)
  have hH : eHid (mW n) ≤ 8 / 1000000 := by
    unfold eHid
    linarith
  have hH0 := eHid_nonneg (mW n)
  have t4 : 2 / √(n : ℝ) ≤ 2 / 64 := by gcongr
  have t40 : 0 ≤ 2 / √(n : ℝ) := by positivity
  have t5 : (1 + 2 / √(n : ℝ)) * eHid (mW n) ≤ (1 + 2 / 64) * (8 / 1000000) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall jCos
  norm_num at t1 t5 ⊢
  linarith

lemma eWr_bound {n : ℕ} (hn : 4096 ≤ n) : eWr (2 * n) n (mW n) ≤ 1837 / 100000 := by
  have hs := sqrt_n_ge hn
  have h1 := sU_bound hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall_bound hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have hq20 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [q_mem.1]
  have t1 : 1 / √(n : ℝ) ≤ 1 / 64 := by gcongr
  have t10 : 0 ≤ 1 / √(n : ℝ) := by positivity
  have t2 : 1 / √(n : ℝ) * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      1 / 64 * (1 - (49372 / 100000) ^ 2 + 2 * (568 / 100000)) :=
    mul_le_mul t1 (by linarith) (by linarith) (by norm_num)
  unfold eWr
  norm_num at t2 ⊢
  linarith

lemma dChi_bound {n : ℕ} (hn : 4096 ≤ n) : dChi n ≤ 6805 / 100000000 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hK := K4_le hn
  have hK0 := K4_nonneg n
  have h2 := sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have t1 : 1 / (4 * (n : ℝ)) ≤ 1 / (4 * 4096) := by gcongr
  have t2 : 3 * √2 / 8 * K4 n / ((n : ℝ) * √(n : ℝ)) ≤
      3 * (141422 / 100000) / 8 * (3466 / 1000) / (4096 * 64) := by
    gcongr
  unfold dChi
  norm_num at t1 t2 ⊢
  linarith

lemma eXr_bound {n : ℕ} (hn : 4096 ≤ n) : eXr n (mA n) (mF n) ≤ 3304 / 100000 := by
  have hs := sqrt_n_ge hn
  have h1 := cF2o_bound hn
  have hd := dChi_bound hn
  have hA := inv_mA_le hn
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hε : epsW (mA n) ≤ 7 / 10000000 := by
    unfold epsW
    nlinarith
  have hsd : √(dA n (mA n)) ≤ 828 / 100000 := by
    refine sqrt_le_of_sq (by norm_num) ?_
    unfold dA
    norm_num at hd hε ⊢
    linarith
  have hsd0 := Real.sqrt_nonneg (dA n (mA n))
  have hq := kappa2_zero_le
  have hq0 := q_mem.1
  have t1 : 1 / √(n : ℝ) ≤ 1 / 64 := by gcongr
  have t2 : kappa (kappa 0) * (2 * √(dA n (mA n))) ≤ 49376 / 100000 * (2 * (828 / 100000)) :=
    mul_le_mul hq (by linarith) (by positivity) (by norm_num)
  unfold eXr
  norm_num at t1 t2 ⊢
  linarith

lemma eV_bound {n : ℕ} (hn : 4096 ≤ n) : eV n (mA n) (mF n) ≤ 23 / 1000 := by
  have hx := nR_ge hn
  have hm := mF_geR hn
  have hA := inv_mA_le hn
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hF : 5 / (mF n : ℝ) ≤ 5 / 262144 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have hF0 : (0 : ℝ) ≤ 5 / (mF n : ℝ) := by
    have : (0 : ℝ) < mF n := by linarith
    positivity
  have hn2 : 2 / (n : ℝ) ≤ 2 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hn20 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have a1 : (1 + 5 / (mF n : ℝ)) ^ 2 ≤ 1 + 39 / 1000000 := by nlinarith
  have a2 : (1 + 5 / (mA n : ℝ)) ^ 2 ≤ 1 + 7 / 10000000 := by nlinarith
  have a12 : (1 + 5 / (mF n : ℝ)) ^ 2 * (1 + 5 / (mA n : ℝ)) ^ 2 ≤
      (1 + 39 / 1000000) * (1 + 7 / 10000000) :=
    mul_le_mul a1 a2 (by positivity) (by norm_num)
  have a123 : (1 + 5 / (mF n : ℝ)) ^ 2 * (1 + 5 / (mA n : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) ≤
      (1 + 39 / 1000000) * (1 + 7 / 10000000) * (1 + 2 / 4096) :=
    mul_le_mul a12 (by linarith) (by linarith) (by norm_num)
  unfold eV
  refine sqrt_le_of_sq (by norm_num) ?_
  norm_num at a123 ⊢
  linarith

/-- **The total at the Focus**: `3·e_P + 2·e_× + e_V ≤ 0.3011` for every `n ≥ 4 096` (`r = 2`). The
value of the bound formula at `n = 4 096` is about `0.280`; the paper total is `0.29086`. -/
theorem vTot_bound {n : ℕ} (hn : 4096 ≤ n) :
    vTot (2 * n) (mW n) n (mA n) (mF n) ≤ 3011 / 10000 := by
  have h1 := eAFr_bound hn
  have h2 := eWr_bound hn
  have h3 := sU_bound hn
  have h4 := eXr_bound hn
  have h5 := eV_bound hn
  unfold vTot
  linarith

/-! ## Items 4 and 5 -/

/-- **`varJ133`: the variance of `J` at the Focus** (`r = 2`, `m_W = ⌈n^{7/2}⌉`, `m_A = n²`,
`m_F = ⌈n^{3/2}⌉`). For every `n ≥ 4 096`: `Var J ≤ (23/25)·((314/1000)·(4/n))²`. -/
theorem varJ133 {n : ℕ} (hn : 4096 ≤ n) :
    Var[Jall; lawAll (2 * n) (mW n) n (mA n) (mF n)] ≤
      23 / 25 * (314 / 1000 * (4 / (n : ℝ))) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hd : dChi n ≤ 1 := by linarith [dChi_bound hn]
  have h := varJ_general (N := 2 * n) hn1 (by omega) (one_le_mW hn1) (one_le_mA hn1)
    (one_le_mF hn1) hd
  have hv := vTot_bound hn
  have hv0 := (vTot_nonneg (2 * n) (mW n) n (mA n) (mF n) (one_le_mF hn1) (one_le_mA hn1) hn1).2.2.2
  refine h.trans ?_
  have hsq : vTot (2 * n) (mW n) n (mA n) (mF n) ^ 2 ≤ (3011 / 10000) ^ 2 :=
    pow_le_pow_left₀ hv0 hv 2
  have h4 : (0 : ℝ) ≤ (4 / (n : ℝ)) ^ 2 := by positivity
  have e : (4 / (n : ℝ) * vTot (2 * n) (mW n) n (mA n) (mF n)) ^ 2 =
      (4 / (n : ℝ)) ^ 2 * vTot (2 * n) (mW n) n (mA n) (mF n) ^ 2 := by ring
  rw [e]
  have e2 : 23 / 25 * (314 / 1000 * (4 / (n : ℝ))) ^ 2 =
      (4 / (n : ℝ)) ^ 2 * (23 / 25 * (314 / 1000) ^ 2) := by ring
  rw [e2]
  refine mul_le_mul_of_nonneg_left (hsq.trans ?_) h4
  norm_num

lemma hjV133 {n : ℕ} (hn : 4096 ≤ n) :
    (1 : ℝ) / 16 ≤ 3 / 25 * ((314 / 1000 * (4 / (n : ℝ))) ^ 2 /
      ((314 / 1000 * (4 / (n : ℝ))) ^ 2 + 23 / 25 * (314 / 1000 * (4 / (n : ℝ))) ^ 2)) := by
  have hj := meanJ132_pos hn
  have hj2 : 0 < (314 / 1000 * (4 / (n : ℝ))) ^ 2 := by positivity
  have e : (314 / 1000 * (4 / (n : ℝ))) ^ 2 /
      ((314 / 1000 * (4 / (n : ℝ))) ^ 2 + 23 / 25 * (314 / 1000 * (4 / (n : ℝ))) ^ 2) = 25 / 48 := by
    field_simp
    ring
  rw [e]
  norm_num

universe w

/-- **`thmC133`: Theorem C with no hypothesis** (`r = 2`, the widths of the Focus, every
`n ≥ 4 096`). The set of `(W, F)` with conditional separation probability at least `1/40` is
measurable and has probability at least `1/26`; for every `(W, F)` in it, every estimator
`c(ω)` that reads nothing of `A` (random bits `ω` independent of `A`) fails at accuracy `1/2`
with probability at least `1/80` over `(A, ω)`: `|c − B(W, A, F)| > sd(W, A, F)/2`. -/
theorem thmC133 {n : ℕ} (hn : 4096 ≤ n) :
    MeasurableSet {x : MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1 |
      1 / 40 ≤ sepProbN (mA n) x.1 x.2} ∧
    1 / 26 ≤ (lawWF (2 * n) (mW n) n (mF n)).real {x | 1 / 40 ≤ sepProbN (mA n) x.1 x.2} ∧
    ∀ (W : MlpParam (2 * n) (mW n) n) (F : MlpParam n (mF n) 1), 1 / 40 ≤ sepProbN (mA n) W F →
      ∀ (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
        (c : Ω' → ℝ), Measurable c →
        1 / 80 ≤ ((mlpGauss n (mA n) n).prod ν).real
          {q : MlpParam n (mA n) n × Ω' | sdn W q.1 F / 2 < |c q.2 - Bn W q.1 F|} :=
  thmC_of_var132.{w} hn (varJ133 hn) (hjV133 hn)

/-- **The separation statement**: for every `n ≥ 4 096`,
`Pr(|B_A − B_{A′}| > (s_A + s_{A′})/2) ≥ 1/16` over `(W, F, A, A′)`. -/
theorem sep133 {n : ℕ} (hn : 4096 ≤ n) :
    1 / 16 ≤ (lawAll (2 * n) (mW n) n (mA n) (mF n)).real sepEvent := by
  have hn1 : 1 ≤ n := by omega
  have h := thmC_of_meanVar (N := 2 * n) (mW := mW n) (mA := mA n) (mF := mF n) hn1 (by omega)
    (meanJ132_pos hn) (meanJ132 hn) (varJ133 hn)
  exact (hjV133 hn).trans h

end BstLean.Part133

open BstLean.Part133 in
#print axioms kernels_general
open BstLean.Part133 in
#print axioms var_P_le_var_k
open BstLean.Part133 in
#print axioms varJ_general
open BstLean.Part133 in
#print axioms vTot_bound
open BstLean.Part133 in
#print axioms varJ133
open BstLean.Part133 in
#print axioms thmC133
open BstLean.Part133 in
#print axioms sep133
