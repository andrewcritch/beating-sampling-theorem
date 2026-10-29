import BstLean.Part142KernD
import BstLean.Part142AgentD
import BstLean.Part142ReluD
import BstLean.Part142LinD
import BstLean.Part142Core

/-!
# Part 142, items 2 to 4, first form: the spread through the DISTANCE kernel

Role: `delegations/statements/p142-spec.md`, items 2 (`kernel142`), 3 (`spread142`) and 4.

Part 139 bounds `E(sd² − S(1 − Q))²` by `S²·((e_V + e_P)² + 2e_P²)`: the diagonal kernel and the
pair kernel separately. Here it is bounded by `3·S²·e_D²`, with `e_D` the `L²` error of the
distance kernel `kD = (k(u,u) + k(u′,u′))/2 − k(u,u′)` around `S(1 − Q)` (`spread_L2_dist`);
the fluctuation that the diagonal and the pair kernel have in common cancels in `kD`.

* `kernDist142a`: `‖kD − S(1 − Q)‖₂ ≤ S·eD142a n` at the widths of the Focus, `n ≥ 4096`, with
  the Lipschitz links of the distance form (`Part142AgentD`, `Part142FD`) and the chord of
  `κ^{∘4}` (`Part142Anchor`); `eD142a_scale`: `eD142a n ≤ 2.28/√n`.
* `spreadLow142_of`: `Pr(sd² < θ·S(1 − Q)) ≤ 3e²/((1 − θ)(1 − Q))²` from `‖kD − S(1 − Q)‖₂ ≤ S·e`.
* `progDist142`: the rate of the program of Part 141 from a bound `e ≤ c_e/√n`.
* `arithProgSucceeds142a`: `Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 742/n + 100/k)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

/-- `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ tauW142 n` (Part 133: World link and link of the inputs). -/
noncomputable def tauW142 (n : ℕ) : ℝ := eWr (2 * n) n (mW n) + sU (2 * n)

lemma tauW142_nonneg {n : ℕ} (hn : 4096 ≤ n) : 0 ≤ tauW142 n := by
  have hsU := sU_nonneg (2 * n)
  have hq := q_mem
  have hsm := eWsmall_nonneg n (mW n)
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hn' : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hW0 : 0 ≤ eWr (2 * n) n (mW n) := by unfold eWr; positivity
  unfold tauW142
  linarith

lemma tauW142_scale {n : ℕ} (hn : 4096 ≤ n) : tauW142 n ≤ 15375 / 10000 / √(n : ℝ) := by
  have h2 := eWr_scale hn
  have h3 := sU_scale hn
  unfold tauW142
  have e : (15375 : ℝ) / 10000 / √(n : ℝ) = 11746 / 10000 / √(n : ℝ) + 3629 / 10000 / √(n : ℝ) := by
    ring
  rw [e]
  linarith

/-- The constants of the distance kernel at fixed inputs:
`gD0 + gD1·(1 − κ(κ(t))) + gD2·(1 − t)`. -/
noncomputable def gD0 (n : ℕ) : ℝ :=
  2 * f1 (mF n) * dA0 n (mA n) +
    2 * f2 (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) +
    2 * f3 (mF n) * √(eps4 n (mA n)) + f4 * cAdlt n (mA n) + cA0 n (mA n)

noncomputable def gD1 (n : ℕ) : ℝ := 2 * f1 (mF n) * dA1 n (mA n) + cA1 n (mA n)

noncomputable def gD2 (n : ℕ) : ℝ := 2 * f1 (mF n) * dA2 n (mA n) + cA2 n (mA n)

/-- The `L²` error of the distance kernel, first form: `‖kD − S(1 − Q)‖₂ ≤ S·eD142a n`. -/
noncomputable def eD142a (n : ℕ) : ℝ :=
  gD0 n + gD1 n * (1 - kappa^[4] 0 + tauW142 n) +
    gD2 n * (1 - kappa (kappa 0) + tauW142 n) + sig4 * tauW142 n

lemma gD_nonneg (n : ℕ) : 0 ≤ gD0 n ∧ 0 ≤ gD1 n ∧ 0 ≤ gD2 n := by
  have a1 := f1_nonneg (mF n)
  have a2 := f2_nonneg (mF n)
  have a3 := f3_nonneg (mF n)
  have a4 := f4_nonneg
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have c0 := cA0_nonneg n (mA n)
  have c1 := cA1_nonneg n (mA n)
  have c2 := cA2_nonneg n (mA n)
  have hs := Real.sqrt_nonneg (eps4 n (mA n))
  have hN : 0 ≤ (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold gD0; positivity
  · unfold gD1; positivity
  · unfold gD2; positivity

/-- **The distance kernel at fixed unit inputs, at the widths of the Focus.** -/
theorem kernD_fixed142a {n : ℕ} (hn : 4096 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) :
    L2le ((mlpGauss n (mA n) n).prod ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
      (fun p : MlpParam n (mA n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
        kernD p.2.2 p.1 x x' - 4 / (n : ℝ) * (1 - kappa^[4] (dotp x x')))
      (4 / (n : ℝ) * (gD0 n + gD1 n * (1 - kappa (kappa (dotp x x'))) +
        gD2 n * (1 - dotp x x'))) := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have ht := dotp_unit_mem hx hx'
  have hkt := kk_memIcc ht
  have u1 : 0 ≤ 1 - kappa (kappa (dotp x x')) := by linarith [hkt.2]
  have u2 : 0 ≤ 1 - dotp x x' := by linarith [ht.2]
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have c0 := cA0_nonneg n (mA n)
  have c1 := cA1_nonneg n (mA n)
  have c2 := cA2_nonneg n (mA n)
  have h := kernD_fixed_of (mF := mF n) hn1 hmA hx hx' (f1_nonneg (mF n)) (f2_nonneg (mF n))
    (f3_nonneg (mF n)) f4_nonneg
    (α := cA0 n (mA n) + cA1 n (mA n) * (1 - kappa (kappa (dotp x x'))) +
      cA2 n (mA n) * (1 - dotp x x'))
    (δ1 := dA0 n (mA n) + dA1 n (mA n) * (1 - kappa (kappa (dotp x x'))) +
      dA2 n (mA n) * (1 - dotp x x'))
    (δ2 := cAdlt n (mA n)) (by positivity) (by positivity) b3
    (fun y y' => F_dist_L2_of reluEDStmt reluPhiStmt hn1 hmF y y')
    (agent_phi_L2_of reluSqStmt reluEDStmt reluDltStmt reluPhiStmt linPhiStmt hn1 hmA hx hx')
    (agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (agent_dlt_L2_of reluSqStmt reluDltStmt linDltStmt hn1 hmA hx hx')
  refine h.congr_bound ?_
  unfold gD0 gD1 gD2
  ring

/-- **`kernDist142a` (`kernel142`, first form).** For `n ≥ 4096`, at the widths of the Focus:
`‖kD − (4/n)(1 − κ^{∘6}(0))‖₂ ≤ (4/n)·eD142a n`. -/
theorem kernDist142a {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eD142a n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  obtain ⟨g0, g1, g2⟩ := gD_nonneg n
  have hT := tX_L2_marg (mA := mA n) (mF := mF n) hN
    (tX_L2_focus (mA := mA n) (mF := mF n) hn1 hN hmW)
  exact kernDist_L2_of hn1 hN g0 g1 g2 (tauW142_nonneg hn)
    (fun x x' hx hx' => kernD_fixed142a hn hx hx') hT

lemma one_sub_k4_nonneg : 0 ≤ 1 - kappa^[4] 0 := by
  have := (kGood_iterate 3).le_one KGood.zero_mem
  linarith

lemma one_sub_k4_le : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := by
  have h : 680943 / 1000000 ≤ kappa^[4] 0 := kappa4_zero_ge'
  linarith

lemma eD142a_nonneg {n : ℕ} (hn : 4096 ≤ n) : 0 ≤ eD142a n := by
  obtain ⟨g0, g1, g2⟩ := gD_nonneg n
  have hτ := tauW142_nonneg hn
  have h4 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h2 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have hs := sig4_nonneg
  unfold eD142a
  positivity

/-- Arithmetic: `a ≤ A·t`, `b ≤ B`, `0 ≤ b`, `0 ≤ A·t` give `a·b ≤ (A·B)·t`. -/
lemma mul_le_lin {a b A B t : ℝ} (ha : a ≤ A * t) (hb : b ≤ B) (hb0 : 0 ≤ b) (hA : 0 ≤ A * t) :
    a * b ≤ A * B * t := by
  have := mul_le_mul ha hb hb0 hA
  nlinarith

/-- `gD0 n ≤ 0.7288/√n`, `gD1 n ≤ 2.2836/√n`, `gD2 n ≤ 0.169417/√n` for `n ≥ 4096`. -/
lemma gD_scale {n : ℕ} (hn : 4096 ≤ n) :
    gD0 n ≤ 7288 / 10000 / √(n : ℝ) ∧ gD1 n ≤ 22836 / 10000 / √(n : ℝ) ∧
      gD2 n ≤ 169417 / 1000000 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht64 : t ≤ 1 / 64 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have et2 : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * t ^ 2 := fun c => by rw [et2]; ring
  have ht2 : t ^ 2 ≤ 1 / 64 * t := by nlinarith
  have ht20 : 0 ≤ t ^ 2 := by positivity
  have F1 := f1_scale hn
  have F2 := f2_scale hn
  have F3 := f3_scale hn
  have F4 := f4_le
  have A0 := cA0_le hn
  have A1 := cA1_le hn
  have A2 := cA2_le hn
  have D0 := dA0_le hn
  have D1 := dA1_le hn
  have D2 := dA2_le hn
  have C5 := cAdlt_le hn
  rw [cv] at F1 F2 F3 A0 A1
  rw [cn] at A2 D0 D2 C5
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have f4n := f4_nonneg
  -- bounds by constants
  have D0c : dA0 n (mA n) ≤ 82 / 100 / 4096 := by nlinarith
  have D2c : dA2 n (mA n) ≤ 105 / 10 / 64 * t := by nlinarith
  have C5c : cAdlt n (mA n) ≤ 72 / 10 / 64 * t := by nlinarith
  have A2c : cA2 n (mA n) ≤ 107 / 10 / 64 * t := by nlinarith
  have hN0 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ 100025 / 100000 := by
    have h1 := inv_mA_le hn
    have h10 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
    have h2 := sqrt_one_add_le hn
    have h20 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
    nlinarith
  have hN00 : 0 ≤ (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) := by positivity
  have hE : √(eps4 n (mA n)) ≤ 2214 / 100000 :=
    sqrt_le_of_sq (by norm_num) ((eps4_bound hn).trans (by norm_num))
  have hE0 := Real.sqrt_nonneg (eps4 n (mA n))
  have p1 := mul_le_lin F1 D0c b0 (by positivity)
  have p2 := mul_le_lin F2 hN0 hN00 (by positivity)
  have p3 := mul_le_lin F3 hE hE0 (by positivity)
  have p4 : f4 * cAdlt n (mA n) ≤ 63662 / 100000 * (72 / 10 / 64 * t) :=
    mul_le_mul F4 C5c b3 (by norm_num)
  have p5 := mul_le_lin F1 D1 b1 (by positivity)
  have D2c' : dA2 n (mA n) ≤ 105 / 10 / 64 / 64 := by nlinarith
  have p6 := mul_le_lin F1 D2c' b2 (by positivity)
  rw [cv, cv, cv]
  refine ⟨?_, ?_, ?_⟩
  · unfold gD0
    linarith
  · unfold gD1
    linarith
  · unfold gD2
    linarith

/-- `eD142a n ≤ 2.28/√n` for `n ≥ 4096`. -/
lemma eD142a_scale {n : ℕ} (hn : 4096 ≤ n) : eD142a n ≤ 228 / 100 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht64 : t ≤ 1 / 64 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  obtain ⟨G0, G1, G2⟩ := gD_scale hn
  rw [cv] at G0 G1 G2
  obtain ⟨g0n, g1n, g2n⟩ := gD_nonneg n
  have hτ := tauW142_scale hn
  rw [cv] at hτ
  have hτ0 := tauW142_nonneg hn
  have hτ64 : tauW142 n ≤ 15375 / 10000 / 64 := by nlinarith
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have h20 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have hs4 := sig4_le
  have hs40 := sig4_nonneg
  have r1 := mul_le_lin G1 (show 1 - kappa^[4] 0 + tauW142 n ≤
    319057 / 1000000 + 15375 / 10000 / 64 by linarith) (by linarith) (by positivity)
  have r2 := mul_le_lin G2 (show 1 - kappa (kappa 0) + tauW142 n ≤
    50628 / 100000 + 15375 / 10000 / 64 by linarith) (by linarith) (by positivity)
  have r3 : sig4 * tauW142 n ≤ 4404 / 10000 * (15375 / 10000 * t) :=
    mul_le_mul hs4 hτ hτ0 (by norm_num)
  rw [cv]
  unfold eD142a
  linarith

/-- **The spread from the distance kernel (`spread142`).** For `n ≥ 4096`, `θ < 1`: if
`‖kD − S(1 − Q)‖₂ ≤ S·e` then `Pr_{W,A,F}(sd² < θ·S·(1 − Q)) ≤ 3e²/((1 − θ)(1 − Q))²`. -/
theorem spreadLow142_of {n : ℕ} (hn : 4096 ≤ n) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e))
    {θ : ℝ} (hθ : θ < 1) :
    (mlpTriple 2 n).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤
      3 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h1Q : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hc : (0 : ℝ) < 4 / (n : ℝ) * (1 - kappa^[6] 0) := by positivity
  have h := spreadLow_dist hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) hD hc hθ
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- **The rate of the program from the distance kernel.** For `n ≥ 4096`, `k ≥ 1`,
`0 < θ < 1`: if `‖kD − S(1 − Q)‖₂ ≤ S·e` and `e ≤ c_e/√n`, then
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + (70.0002 + 8.2/(θ q₀) + 3c_e²/((1 − θ)q₀)²)/n +
  (4/(θ q₀))/k)`, `q₀ = 0.222757 ≤ 1 − Q`. -/
theorem progDist142 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {e ce : ℝ} (he : 0 ≤ e) (hce : e ≤ ce / √(n : ℝ))
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    1 - (2 / 1000 + (700002 / 10000 + 82 / 10 / (θ * (222757 / 1000000)) +
          3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hS := spreadLow142_of hn he hD hθ1
  have h := progRate142 hn hk hθ0 hS
  refine le_trans ?_ h
  have hce0 : 0 ≤ ce / √(n : ℝ) := he.trans hce
  have he2 : e ^ 2 ≤ ce ^ 2 / (n : ℝ) := by
    have h1 : e ^ 2 ≤ (ce / √(n : ℝ)) ^ 2 := pow_le_pow_left₀ he hce 2
    rwa [div_pow, Real.sq_sqrt hx0.le] at h1
  have hden : ((1 - θ) * (222757 / 1000000 : ℝ)) ^ 2 ≤ ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hy h1θ.le) 2
  have hpS : 3 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 ≤
      3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / (n : ℝ) := by
    calc 3 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2
        ≤ 3 * e ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ 3 * (ce ^ 2 / (n : ℝ)) / ((1 - θ) * (222757 / 1000000)) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have e1 : (700002 / 10000 + 82 / 10 / (θ * (222757 / 1000000)) +
      3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2) / (n : ℝ) =
      (700002 / 10000 + 82 / 10 / (θ * (222757 / 1000000))) / (n : ℝ) +
        3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / (n : ℝ) := by ring
  rw [e1]
  linarith

/-- **The headline with the Lipschitz links of the distance kernel.** For every `n ≥ 4096`,
`k ≥ 1`: `Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 742/n + 100/k)` (`θ = 0.18`). -/
theorem arithProgSucceeds142a {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 742 / (n : ℝ) + 100 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progDist142 hn hk (θ := 18 / 100) (by norm_num) (by norm_num) (eD142a_nonneg hn)
    (eD142a_scale hn) (kernDist142a hn)
  refine le_trans ?_ h
  have e1 : (700002 / 10000 + 82 / 10 / (18 / 100 * (222757 / 1000000 : ℝ)) +
      3 * (228 / 100 : ℝ) ^ 2 / ((1 - 18 / 100) * (222757 / 1000000)) ^ 2) / (n : ℝ) ≤
      742 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (18 / 100 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 100 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  linarith

end BstLean.Part142

open BstLean.Part142 in
#print axioms kernDist142a
open BstLean.Part142 in
#print axioms eD142a_scale
open BstLean.Part142 in
#print axioms spreadLow142_of
open BstLean.Part142 in
#print axioms progDist142
open BstLean.Part142 in
#print axioms arithProgSucceeds142a
