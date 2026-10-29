import BstLean.Part144JointT
import BstLean.Part144Num2
import BstLean.Part143FinalL

/-!
# Part 144, item 2: the mean of `k` exact samples fails with probability above `1/100`

Role: `delegations/statements/p144-spec.md`, item 2 (`sampleFails144`). Paper: Theorem 4 of
`MM-best-result.md` (round onW15c: every `k ≤ 15` for `n ≥ 15 332`, every `k ≤ 16` for
`n ≥ 16 384`; the route here is not the paper's: see `Part144Struct2`, `Part144Block3`).

At the widths of the Focus, `r = 2`. The event `failSet k` is `|ĝ_k − B| > sd/2`, `ĝ_k` the mean
of `k` independent exact samples `F(A(x(u_j)))`; the probability is joint over `(W, A, F)`
(`mlpTriple 2 n`) and the `k` independent uniform inputs (`uniK k (2n)`).

The kernel bound for `4096 ≤ n` is `kernDist142`, `eD142_scale` of Part 142
(`eD142 n ≤ 1.835/√n`); from `n = 13225` it is `kernDist143`, `eD143_L` of Part 143
(`eD143 n ≤ 1.027/√n`).

* `ratioE_of`: `(e/c)² ≤ δ₂` from a bound `E ≤ a/√n`.
* `failsE_num`: the event method (`sampleFails_of`) at the level `√(9/2)`; used for `k ≤ 5`.
* `failsT_num`: the assembly of `sampleFailsT_of` at a level `t0` with rational bounds of
  `Φ̄(t0)` and `κ = φ(t0)/(2t0)`; used for `k ≥ 6`.
* **`sampleFails144`**: every `n ≥ 13225`, every `1 ≤ k ≤ 25`: `Pr(failSet k) > 1/100`.
* The ladder on the whole frontier interval: **`sampleFails144_4096`** (every `n ≥ 4096`,
  `k ≤ 18`), `sampleFails144_4500` (`k ≤ 19`), `sampleFails144_5500` (`k ≤ 20`),
  `sampleFails144_6500` (`k ≤ 21`), `sampleFails144_8192` (`k ≤ 22`), `sampleFails144_10000`
  (`k ≤ 23`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142 BstLean.Part143

/-- `1 ≤ m_F` for `n ≥ 1`. -/
lemma one_le_mF {n : ℕ} (hn : 1 ≤ n) : 1 ≤ mF n := by
  by_contra h
  have h0 : mF n ≤ 0 := by omega
  have h1 := (mF_le_iff n 0).mp h0
  have h2 : 0 < n ^ 3 := by positivity
  omega

/-! ## Generic numeric steps -/

/-- The ratio `(e/c)²` from a bound `E ≤ a/√n`: `(e/c)² ≤ δ₂` if `a² ≤ δ₂·q₀²·n₀`,
`q₀ = 0.222757 ≤ 1 − κ^{∘6}(0)`. -/
lemma ratioE_of {n n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hn : n₀ ≤ n) {E a δ₂ : ℝ} (hE0 : 0 ≤ E)
    (hδ : 0 ≤ δ₂) (hE : E ≤ a / √(n : ℝ))
    (hnum : a ^ 2 ≤ δ₂ * (222757 / 1000000) ^ 2 * (n₀ : ℝ)) :
    (4 / (n : ℝ) * E) ^ 2 / (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 ≤ δ₂ := by
  have hx : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have h4 : (0 : ℝ) < 4 / (n : ℝ) := by positivity
  have hc : 0 < 4 / (n : ℝ) * (1 - kappa^[6] 0) := mul_pos h4 (by linarith)
  have hc2 : 0 < (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 := by positivity
  rw [div_le_iff₀ hc2]
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hx0.le
  have h1 : E ^ 2 ≤ a ^ 2 / (n : ℝ) := by
    have := pow_le_pow_left₀ hE0 hE 2
    rwa [div_pow, hsq] at this
  have h2 : a ^ 2 / (n : ℝ) ≤ δ₂ * (222757 / 1000000) ^ 2 := by
    rw [div_le_iff₀ hx0]
    have h3 : δ₂ * (222757 / 1000000) ^ 2 * (n₀ : ℝ) ≤ δ₂ * (222757 / 1000000) ^ 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    linarith
  have h3 : ((222757 : ℝ) / 1000000) ^ 2 ≤ (1 - kappa^[6] 0) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hy 2
  have h5 : E ^ 2 ≤ δ₂ * (1 - kappa^[6] 0) ^ 2 :=
    (h1.trans h2).trans (mul_le_mul_of_nonneg_left h3 hδ)
  have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg (4 / (n : ℝ)))
  calc (4 / (n : ℝ) * E) ^ 2 = (4 / (n : ℝ)) ^ 2 * E ^ 2 := by ring
    _ ≤ (4 / (n : ℝ)) ^ 2 * (δ₂ * (1 - kappa^[6] 0) ^ 2) := h6
    _ = δ₂ * (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 := by ring

/-- **The event method at the level `t0 = √(9/2)`, any kernel bound `E`.** `δ₂` bounds `(e/c)²`,
`ρ` bounds `K/(18 − k)²` with `K = 648 + (18 − k)² + (81/4)k²`. -/
theorem failsE_num {n : ℕ} (hn : 4096 ≤ n) {E : ℝ}
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * E))
    {k : ℕ} (hk1 : 1 ≤ k) (hk18 : k < 18) {δ₂ ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hδ : (4 / (n : ℝ) * E) ^ 2 / (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 ≤ δ₂)
    (hρ : 32 * (81 / 4 : ℝ) + (4 * (9 / 2) - (k : ℝ)) ^ 2 + 81 / 4 * (k : ℝ) ^ 2 ≤
      ρ * (4 * (9 / 2) - (k : ℝ)) ^ 2)
    (hfin : (1 : ℝ) / 100 ≤ 161 / 10000 * (1 - ρ * δ₂)) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF := one_le_mF hn1
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  set e : ℝ := 4 / (n : ℝ) * E with he
  have hc0 : 0 < c := mul_pos (by positivity) (by linarith)
  set t0 : ℝ := √(9 / 2) with ht0d
  have ht0 : 0 < t0 := Real.sqrt_pos.mpr (by norm_num)
  have ht2 : t0 ^ 2 = 9 / 2 := Real.sq_sqrt (by norm_num)
  have ht4 : t0 ^ 4 = 81 / 4 := by
    have : t0 ^ 4 = (t0 ^ 2) ^ 2 := by ring
    rw [this, ht2]; norm_num
  have hkR : (k : ℝ) < 18 := by exact_mod_cast hk18
  have hgap : (k : ℝ) < 4 * t0 ^ 2 := by rw [ht2]; linarith
  have h := sampleFails_of (N := 2 * n) (mW := mW n) (n := n) (mA := mA n) (mF := mF n)
    hn1 hN hmF hk1 hc0 hD ht0 hgap
  rw [ht4, ht2] at h
  set g : ℝ := 4 * (9 / 2) - (k : ℝ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set K : ℝ := 32 * (81 / 4 : ℝ) + g ^ 2 + 81 / 4 * (k : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hδ0 : 0 ≤ e ^ 2 / c ^ 2 := by positivity
  have hx1 : K * e ^ 2 / (g * c) ^ 2 ≤ ρ * δ₂ := by
    have e1 : K * e ^ 2 / (g * c) ^ 2 = K / g ^ 2 * (e ^ 2 / c ^ 2) := by
      field_simp
    rw [e1]
    have h1 : K / g ^ 2 ≤ ρ := by
      rw [div_le_iff₀ (by positivity)]; exact hρ
    exact mul_le_mul h1 hδ hδ0 hρ0
  have hT := tail_144
  rw [← ht0d] at hT
  have hpos : 0 < 1 - ρ * δ₂ := by
    by_contra hcon
    have : 1 - ρ * δ₂ ≤ 0 := not_lt.mp hcon
    nlinarith
  have h1 : 1 - ρ * δ₂ ≤ 1 - K * e ^ 2 / (g * c) ^ 2 := by linarith
  have h2 : (161 : ℝ) / 10000 * (1 - ρ * δ₂) <
      (gaussianReal 0 1).real (Ioi t0) * (1 - K * e ^ 2 / (g * c) ^ 2) :=
    mul_lt_mul hT h1 hpos measureReal_nonneg
  have h3 : (1 : ℝ) / 100 < ((lawT (2 * n) (mW n) n (mA n) (mF n)).prod
      (uniK k (2 * n))).real (failSet k) := by linarith
  exact h3

/-- **The assembly of `sampleFailsT_of` at a level `t0`, `t0² = z`, any kernel bound `E`.**
`Tl ≤ Φ̄(t0)`, `κl ≤ κ ≤ κh` with `κ = φ(t0)/(2t0)`, `2κh(2 + z) ≤ 3/25` (so that
`2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)`), `δ₂` bounds `(e/c)²`. With `Ah = 2(Tl + κh·z)`, `Al = 2(Tl + κl·z)`,
`bl = 2κl·k/4`, `bh = 2κh·k/4`, `v₀ = (Ah − bl)/(2βl)`, `βl = Al³k/(4bh²)`, `βh = Ah³k/(4bl²)`,
`αh = 2Ah(k − 1)/k` and `C_m = αh + βh/(1 − v₀)²`: if `v₀ < 1` and
`2(Tl + κl(z − k/4)) − C_m·δ₂ > 1/100`, then `Pr(failSet k) > 1/100`. -/
theorem failsT_num {n : ℕ} (hn : 4096 ≤ n) {E : ℝ}
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * E))
    {k : ℕ} (hk2 : 2 ≤ k) {δ₂ : ℝ}
    (hδ : (4 / (n : ℝ) * E) ^ 2 / (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 ≤ δ₂)
    {t0 z Tl κl κh : ℝ} (ht0 : 0 < t0) (ht2 : t0 ^ 2 = z) (hTl0 : 0 ≤ Tl)
    (hTl : Tl ≤ (gaussianReal 0 1).real (Ioi t0)) (hκl0 : 0 < κl)
    (hκl : κl ≤ gaussianPDFReal 0 1 t0 / (2 * t0)) (hκh : gaussianPDFReal 0 1 t0 / (2 * t0) ≤ κh)
    (hH : 2 * κh * (2 + z) ≤ 3 / 25) (hk4 : (k : ℝ) ≤ 4 * z)
    (hv1 : ((2 * (Tl + κh * z)) - 2 * (κl * ((k : ℝ) / 4))) /
      (2 * ((2 * (Tl + κl * z)) ^ 3 * (k : ℝ) / (4 * (2 * (κh * ((k : ℝ) / 4))) ^ 2))) < 1)
    (hfin : (1 : ℝ) / 100 < 2 * (Tl + κl * (z - (k : ℝ) / 4)) -
      (2 * (2 * (Tl + κh * z)) * ((k : ℝ) - 1) / (k : ℝ) +
        (2 * (Tl + κh * z)) ^ 3 * (k : ℝ) / (4 * (2 * (κl * ((k : ℝ) / 4))) ^ 2) /
          (1 - ((2 * (Tl + κh * z)) - 2 * (κl * ((k : ℝ) / 4))) /
            (2 * ((2 * (Tl + κl * z)) ^ 3 * (k : ℝ) /
              (4 * (2 * (κh * ((k : ℝ) / 4))) ^ 2)))) ^ 2) * δ₂) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF := one_le_mF hn1
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  set e : ℝ := 4 / (n : ℝ) * E with he
  have hc0 : 0 < c := mul_pos (by positivity) (by linarith)
  have hkR2 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < k := by linarith
  have hz0 : 0 < z := by rw [← ht2]; positivity
  set κ : ℝ := gaussianPDFReal 0 1 t0 / (2 * t0) with hκ
  have hκ0 : 0 < κ := lt_of_lt_of_le hκl0 hκl
  have hκh0 : 0 < κh := lt_of_lt_of_le hκ0 hκh
  -- the exact and the rational quantities
  set Ac : ℝ := 2 * (Tl + κ * z) with hAc
  set b : ℝ := 2 * (κ * ((k : ℝ) / 4)) with hb
  set Ah : ℝ := 2 * (Tl + κh * z) with hAh
  set Al : ℝ := 2 * (Tl + κl * z) with hAl
  set bl : ℝ := 2 * (κl * ((k : ℝ) / 4)) with hbl
  set bh : ℝ := 2 * (κh * ((k : ℝ) / 4)) with hbh
  have hAl0 : 0 < Al := by rw [hAl]; positivity
  have hAlA : Al ≤ Ac := by
    rw [hAl, hAc]; have := mul_le_mul_of_nonneg_right hκl hz0.le; linarith
  have hAc0 : 0 < Ac := lt_of_lt_of_le hAl0 hAlA
  have hAA : Ac ≤ Ah := by
    rw [hAc, hAh]; have := mul_le_mul_of_nonneg_right hκh hz0.le; linarith
  have hAh0 : 0 < Ah := lt_of_lt_of_le hAc0 hAA
  have hbl0 : 0 < bl := by rw [hbl]; positivity
  have hbb : bl ≤ b := by
    have := mul_le_mul_of_nonneg_right hκl (by positivity : (0 : ℝ) ≤ (k : ℝ) / 4)
    rw [hbl, hb]; linarith
  have hb0 : 0 < b := lt_of_lt_of_le hbl0 hbb
  have hbbh : b ≤ bh := by
    have := mul_le_mul_of_nonneg_right hκh (by positivity : (0 : ℝ) ≤ (k : ℝ) / 4)
    rw [hb, hbh]; linarith
  have hbh0 : 0 < bh := lt_of_lt_of_le hb0 hbbh
  have hAb0 : 0 ≤ Ac - b := by
    have : κ * ((k : ℝ) / 4) ≤ κ * z := mul_le_mul_of_nonneg_left (by linarith) hκ0.le
    rw [hAc, hb]; linarith
  -- `β` and its bounds
  set β : ℝ := Ac ^ 3 * (k : ℝ) / (4 * b ^ 2) with hβd
  set βh : ℝ := Ah ^ 3 * (k : ℝ) / (4 * bl ^ 2) with hβh
  set βl : ℝ := Al ^ 3 * (k : ℝ) / (4 * bh ^ 2) with hβl
  have hβl0 : 0 < βl := by rw [hβl]; positivity
  have hββh : β ≤ βh := by
    have hA3 : Ac ^ 3 ≤ Ah ^ 3 := pow_le_pow_left₀ hAc0.le hAA 3
    have hb2 : bl ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hbl0.le hbb 2
    exact div_le_div₀ (mul_nonneg (pow_nonneg hAh0.le 3) hk0.le)
      (mul_le_mul_of_nonneg_right hA3 hk0.le) (by positivity) (by linarith)
  have hβlβ : βl ≤ β := by
    have hA3 : Al ^ 3 ≤ Ac ^ 3 := pow_le_pow_left₀ hAl0.le hAlA 3
    have hb2 : b ^ 2 ≤ bh ^ 2 := pow_le_pow_left₀ hb0.le hbbh 2
    exact div_le_div₀ (mul_nonneg (pow_nonneg hAc0.le 3) hk0.le)
      (mul_le_mul_of_nonneg_right hA3 hk0.le) (by positivity) (by linarith)
  have hβ0 : 0 < β := lt_of_lt_of_le hβl0 hβlβ
  have hβh0 : 0 < βh := lt_of_lt_of_le hβ0 hββh
  -- `α` and its bound
  have hk1k : 1 ≤ ((k : ℝ) - 1) := by linarith
  have hfr : 1 ≤ 2 * ((k : ℝ) - 1) / (k : ℝ) := by
    rw [le_div_iff₀ hk0]; linarith
  set α : ℝ := 2 * Ac * ((k : ℝ) - 1) / (k : ℝ) with hαd
  set αh : ℝ := 2 * Ah * ((k : ℝ) - 1) / (k : ℝ) with hαh
  have hααh : α ≤ αh := by
    rw [hαd, hαh]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hk0.le
  have hαA : Ah ≤ αh := by
    have e1 : αh = Ah * (2 * ((k : ℝ) - 1) / (k : ℝ)) := by rw [hαh]; ring
    rw [e1]; exact le_mul_of_one_le_right hAh0.le hfr
  have hα0 : 0 ≤ α := by rw [hαd]; positivity
  -- `v₀` and `C_m`
  set ah : ℝ := Ah - bl with hah
  have hah0 : 0 ≤ ah := by rw [hah]; linarith
  set v0 : ℝ := ah / (2 * βl) with hv0d
  have hv00 : 0 ≤ v0 := by rw [hv0d]; positivity
  have hv01 : v0 < 1 := hv1
  have h1v : 0 < 1 - v0 := by linarith
  set Cm : ℝ := αh + βh / (1 - v0) ^ 2 with hCm
  have hCmα : αh < Cm := by
    rw [hCm]; have : 0 < βh / (1 - v0) ^ 2 := by positivity
    linarith
  have hCm0 : 0 < Cm := lt_of_lt_of_le hAh0 (hαA.trans hCmα.le)
  have hC1 : Ac - b ≤ Cm := by
    have : Ac - b ≤ Ah := by linarith
    linarith
  have hC2 : 2 * Ac / (k : ℝ) ≤ Cm := by
    have h1 : 2 * Ac / (k : ℝ) ≤ αh := by
      rw [hαh]
      refine div_le_div_of_nonneg_right ?_ hk0.le
      have h2 := mul_le_mul_of_nonneg_left hk1k (by linarith : (0 : ℝ) ≤ 2 * Ah)
      linarith
    linarith
  have hCα : α < Cm := lt_of_le_of_lt hααh hCmα
  have hav : (Ac - b) * (Cm - α) ≤ 2 * β * Cm * v0 := by
    have h1 : (Ac - b) * (Cm - α) ≤ ah * Cm :=
      mul_le_mul (by rw [hah]; linarith) (by linarith) (by linarith) hah0
    have h2 : ah = 2 * βl * v0 := by rw [hv0d]; field_simp
    have h3 : 2 * βl * v0 * Cm ≤ 2 * β * v0 * Cm := by
      have : 2 * βl * v0 ≤ 2 * β * v0 :=
        mul_le_mul_of_nonneg_right (by linarith) hv00
      exact mul_le_mul_of_nonneg_right this hCm0.le
    calc (Ac - b) * (Cm - α) ≤ ah * Cm := h1
      _ = 2 * βl * v0 * Cm := by rw [h2]
      _ ≤ 2 * β * v0 * Cm := h3
      _ = 2 * β * Cm * v0 := by ring
  have hβc : β ≤ (Cm - α) * (1 - v0) ^ 2 := by
    have h1 : βh = (Cm - αh) * (1 - v0) ^ 2 := by rw [hCm]; field_simp; ring
    have h2 : (Cm - αh) * (1 - v0) ^ 2 ≤ (Cm - α) * (1 - v0) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hk4' : (k : ℝ) ≤ 4 * t0 ^ 2 := by rw [ht2]; exact hk4
  -- `2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)`
  have hA1 : 2 * ((gaussianReal 0 1).real (Ioi t0) + κ * t0 ^ 2) ≤
      (gaussianReal 0 1).real (Ioi 1) := by
    have hmu := mills_upper ht0
    have e1 : gaussianPDFReal 0 1 t0 / t0 = 2 * κ := by rw [hκ]; field_simp
    rw [e1] at hmu
    have h1 := BstLean.Part131.tail_one_gt
    have h2 : 2 * κ * (2 + z) ≤ 2 * κh * (2 + z) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    rw [ht2]
    have e3 : 2 * (2 * κ + κ * z) = 2 * κ * (2 + z) := by ring
    linarith
  have h := sampleFailsT_of (N := 2 * n) (mW := mW n) (n := n) (mA := mA n) (mF := mF n)
    hn1 hN hmF hk2 hc0 hD (t0 := t0) (Tl := Tl) (Cm := Cm) (v0 := v0) ht0 hTl0 hTl hA1 hk4'
    (by rw [← hκ, ht2]; exact hC1) (by rw [← hκ, ht2]; exact hC2)
    (by rw [← hκ, ht2]; exact hCα) hv00 hv01.le (by rw [← hκ, ht2]; exact hav)
    (by rw [← hκ, ht2]; exact hβc)
  rw [← hκ, ht2] at h
  set x : ℝ := e ^ 2 / c ^ 2 with hxd
  have hx0' : 0 ≤ x := by positivity
  have hxδ : x ≤ δ₂ := hδ
  have e2 : Cm * e ^ 2 / c ^ 2 = Cm * x := by rw [hxd]; ring
  rw [e2] at h
  have hloss : Cm * x ≤ Cm * δ₂ := mul_le_mul_of_nonneg_left hxδ hCm0.le
  have hM : 2 * (Tl + κl * (z - (k : ℝ) / 4)) ≤ Ac - b := by
    have h1 : κl * (z - (k : ℝ) / 4) ≤ κ * (z - (k : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hκl (by linarith)
    have e3 : Ac - b = 2 * (Tl + κ * (z - (k : ℝ) / 4)) := by rw [hAc, hb]; ring
    rw [e3]; linarith
  have h3 : (1 : ℝ) / 100 < ((lawT (2 * n) (mW n) n (mA n) (mF n)).prod
      (uniK k (2 * n))).real (failSet k) := by linarith
  exact h3

/-- **One rung**: for a kernel bound `E` with `(e/c)² ≤ δ₂ ≤ 0.016568`: the event method for
`k ≤ 5` and `failsT_num` at a level `t0` for `6 ≤ k ≤ K`. -/
theorem rungT {n : ℕ} (hn4 : 4096 ≤ n) {E : ℝ}
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * E))
    {δ₂ : ℝ} (hδ16 : δ₂ ≤ 16568 / 1000000)
    (hr : (4 / (n : ℝ) * E) ^ 2 / (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 ≤ δ₂)
    {t0 z Tl κl κh : ℝ} (ht0 : 0 < t0) (ht2 : t0 ^ 2 = z) (hTl0 : 0 ≤ Tl)
    (hTl : Tl ≤ (gaussianReal 0 1).real (Ioi t0)) (hκl0 : 0 < κl)
    (hκl : κl ≤ gaussianPDFReal 0 1 t0 / (2 * t0)) (hκh : gaussianPDFReal 0 1 t0 / (2 * t0) ≤ κh)
    (hH : 2 * κh * (2 + z) ≤ 3 / 25) {K : ℕ}
    (hbig : ∀ j : ℕ, 6 ≤ j → j ≤ K → (j : ℝ) ≤ 4 * z ∧
      (((2 * (Tl + κh * z)) - 2 * (κl * ((j : ℝ) / 4))) /
        (2 * ((2 * (Tl + κl * z)) ^ 3 * (j : ℝ) / (4 * (2 * (κh * ((j : ℝ) / 4))) ^ 2))) < 1) ∧
      ((1 : ℝ) / 100 < 2 * (Tl + κl * (z - (j : ℝ) / 4)) -
        (2 * (2 * (Tl + κh * z)) * ((j : ℝ) - 1) / (j : ℝ) +
          (2 * (Tl + κh * z)) ^ 3 * (j : ℝ) / (4 * (2 * (κl * ((j : ℝ) / 4))) ^ 2) /
            (1 - ((2 * (Tl + κh * z)) - 2 * (κl * ((j : ℝ) / 4))) /
              (2 * ((2 * (Tl + κl * z)) ^ 3 * (j : ℝ) /
                (4 * (2 * (κh * ((j : ℝ) / 4))) ^ 2)))) ^ 2) * δ₂))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ K) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  rcases Nat.lt_or_ge k 6 with h6 | h6
  · refine failsE_num hn4 hD hk1 (by omega) (ρ := 8) (by norm_num) hr ?_ ?_
    · interval_cases k <;> norm_num
    · have : (8 : ℝ) * δ₂ ≤ 8 * (16568 / 1000000) := mul_le_mul_of_nonneg_left hδ16 (by norm_num)
      linarith
  · obtain ⟨h4, hv, hf⟩ := hbig k h6 hk
    exact failsT_num hn4 hD (by omega) hr ht0 ht2 hTl0 hTl hκl0 hκl hκh hH h4 hv hf

/-! ## The ladder with the kernel bound of Part 142: every `n ≥ 4096` -/

/-- The ratio `(e/c)²` for the kernel bound of Part 142, `n ≥ n₀ ≥ 4096`. -/
lemma ratio142 {n n₀ : ℕ} (hn₀ : 4096 ≤ n₀) (hn : n₀ ≤ n) {δ₂ : ℝ} (hδ0 : 0 ≤ δ₂)
    (hnum : (1835 / 1000 : ℝ) ^ 2 ≤ δ₂ * (222757 / 1000000) ^ 2 * (n₀ : ℝ)) :
    (4 / (n : ℝ) * eD142 n) ^ 2 / (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 ≤ δ₂ :=
  ratioE_of (n₀ := n₀) (by omega) hn (a := 1835 / 1000) (eD142_nonneg (by omega)) hδ0
    (eD142_scale (by omega)) hnum

/-- `Φ̄(√5) ≥ 0.012624` (the four-term Mills bound). -/
lemma tail4_5 : (12624 : ℝ) / 1000000 ≤ (gaussianReal 0 1).real (Ioi (√5)) := by
  obtain ⟨_, hEu⟩ := exp_five_half_bounds
  have hT := tail4_of_mills (z := 5) (tl := 2236067 / 1000000) (E := 1218250 / 100000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hEu
  exact le_trans (by norm_num) hT

/-- `20.085536 ≤ exp 3 ≤ 20.085537`. -/
lemma exp_three_bounds :
    (20085536 : ℝ) / 1000000 ≤ Real.exp 3 ∧ Real.exp 3 ≤ 20085537 / 1000000 := by
  have h1 := Real.exp_one_gt_d9
  have h1' := Real.exp_one_lt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hl : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hu : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ h1' (Real.exp_pos 1).le (by norm_num)
  rw [e]
  constructor
  · norm_num at hl ⊢; linarith
  · norm_num at hu ⊢; linarith

/-- The level `t0 = √6`: `Φ̄(√6) ≥ 0.0071355` and `0.00405434 ≤ φ(√6)/(2√6) ≤ 0.00405436`. -/
lemma level6 : (71355 : ℝ) / 10000000 ≤ (gaussianReal 0 1).real (Ioi (√6)) ∧
    (405434 : ℝ) / 100000000 ≤ gaussianPDFReal 0 1 (√6) / (2 * √6) ∧
    gaussianPDFReal 0 1 (√6) / (2 * √6) ≤ 405436 / 100000000 := by
  obtain ⟨hEl, hEu⟩ := exp_three_bounds
  have hz : (0 : ℝ) < 6 := by norm_num
  have hE' : Real.exp ((6 : ℝ) / 2) ≤ 20085537 / 1000000 := by
    rw [show ((6 : ℝ) / 2) = 3 by norm_num]; exact hEu
  have hE'' : (20085536 : ℝ) / 1000000 ≤ Real.exp ((6 : ℝ) / 2) := by
    rw [show ((6 : ℝ) / 2) = 3 by norm_num]; exact hEl
  have hT := tail4_of_mills (z := 6) (tl := 2449489 / 1000000) (E := 20085537 / 1000000)
    hz (by norm_num) (by norm_num) (by norm_num) hE'
  obtain ⟨hκl, hκh⟩ := kappa_bounds_of (z := 6) (tl := 2449489 / 1000000)
    (tu := 2449490 / 1000000) (El := 20085536 / 1000000) (Eu := 20085537 / 1000000) hz
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hE'' hE'
  exact ⟨le_trans (by norm_num) hT, le_trans (by norm_num) hκl, le_trans hκh (by norm_num)⟩

/-- `22.75989 ≤ exp(25/8) ≤ 22.75990`. -/
lemma exp_258_bounds :
    (2275989 : ℝ) / 100000 ≤ Real.exp (25 / 8) ∧ Real.exp (25 / 8) ≤ 2275990 / 100000 := by
  obtain ⟨h3l, h3u⟩ := exp_three_bounds
  have h1 := Real.exp_one_gt_d9
  have h1' := Real.exp_one_lt_d9
  have hp : 0 < Real.exp (1 / 8) := Real.exp_pos _
  have h8 : Real.exp (1 / 8) ^ 8 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hl : (11331484 : ℝ) / 10000000 ≤ Real.exp (1 / 8) := by
    by_contra hcon
    have hlt : Real.exp (1 / 8) < 11331484 / 10000000 := not_le.mp hcon
    have h9 : Real.exp (1 / 8) ^ 8 < (11331484 / 10000000 : ℝ) ^ 8 :=
      pow_lt_pow_left₀ hlt hp.le (by norm_num)
    rw [h8] at h9
    norm_num at h9 h1
    linarith
  have hu : Real.exp (1 / 8) ≤ 11331485 / 10000000 := by
    by_contra hcon
    have hlt : (11331485 / 10000000 : ℝ) < Real.exp (1 / 8) := not_le.mp hcon
    have h9 : (11331485 / 10000000 : ℝ) ^ 8 < Real.exp (1 / 8) ^ 8 :=
      pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
    rw [h8] at h9
    norm_num at h9 h1'
    linarith
  have e : Real.exp (25 / 8) = Real.exp 3 * Real.exp (1 / 8) := by
    rw [← Real.exp_add]; norm_num
  rw [e]
  have hp3 : 0 < Real.exp 3 := Real.exp_pos _
  constructor
  · nlinarith
  · nlinarith

/-- **Every `n ≥ 4096`, every `1 ≤ k ≤ 18`: the mean of `k` independent exact samples fails
(`|ĝ_k − B| > sd/2`) with probability above `1/100`.** -/
theorem sampleFails144_4096 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 18) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  refine rungT hn4 (kernDist142 hn4) (δ₂ := 16568 / 1000000) (by norm_num)
    (ratio142 (n₀ := 4096) (by norm_num) hn (by norm_num) (by norm_num))
    (t0 := √5) (z := 5) (Tl := 12624 / 1000000)
    (κl := 7322 / 1000000) (κh := 7323 / 1000000) (Real.sqrt_pos.mpr (by norm_num))
    (Real.sq_sqrt (by norm_num)) (by norm_num) tail4_5 (by norm_num) kappa5_lower kappa5_upper
    (by norm_num)
    (K := 18) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **Every `n ≥ 4500`, every `1 ≤ k ≤ 19`: the mean of `k` independent exact samples fails
(`|ĝ_k − B| > sd/2`) with probability above `1/100`.** -/
theorem sampleFails144_4500 {n : ℕ} (hn : 4500 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 19) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  refine rungT hn4 (kernDist142 hn4) (δ₂ := 150799 / 10000000) (by norm_num)
    (ratio142 (n₀ := 4500) (by norm_num) hn (by norm_num) (by norm_num))
    (t0 := √5) (z := 5) (Tl := 12624 / 1000000)
    (κl := 7322 / 1000000) (κh := 7323 / 1000000) (Real.sqrt_pos.mpr (by norm_num))
    (Real.sq_sqrt (by norm_num)) (by norm_num) tail4_5 (by norm_num) kappa5_lower kappa5_upper
    (by norm_num)
    (K := 19) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **Every `n ≥ 5500`, every `1 ≤ k ≤ 20`: the mean of `k` independent exact samples fails
(`|ĝ_k − B| > sd/2`) with probability above `1/100`.** -/
theorem sampleFails144_5500 {n : ℕ} (hn : 5500 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 20) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  refine rungT hn4 (kernDist142 hn4) (δ₂ := 123381 / 10000000) (by norm_num)
    (ratio142 (n₀ := 5500) (by norm_num) hn (by norm_num) (by norm_num))
    (t0 := √5) (z := 5) (Tl := 12624 / 1000000)
    (κl := 7322 / 1000000) (κh := 7323 / 1000000) (Real.sqrt_pos.mpr (by norm_num))
    (Real.sq_sqrt (by norm_num)) (by norm_num) tail4_5 (by norm_num) kappa5_lower kappa5_upper
    (by norm_num)
    (K := 20) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **Every `n ≥ 6500`, every `1 ≤ k ≤ 21`: the mean of `k` independent exact samples fails
(`|ĝ_k − B| > sd/2`) with probability above `1/100`.** -/
theorem sampleFails144_6500 {n : ℕ} (hn : 6500 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 21) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  refine rungT hn4 (kernDist142 hn4) (δ₂ := 104399 / 10000000) (by norm_num)
    (ratio142 (n₀ := 6500) (by norm_num) hn (by norm_num) (by norm_num))
    (t0 := √6) (z := 6) (Tl := 71355 / 10000000)
    (κl := 405434 / 100000000) (κh := 405436 / 100000000) (Real.sqrt_pos.mpr (by norm_num))
    (Real.sq_sqrt (by norm_num)) (by norm_num) level6.1 (by norm_num) level6.2.1 level6.2.2
    (by norm_num)
    (K := 21) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **Every `n ≥ 8192`, every `1 ≤ k ≤ 22`: the mean of `k` independent exact samples fails
(`|ĝ_k − B| > sd/2`) with probability above `1/100`.** -/
theorem sampleFails144_8192 {n : ℕ} (hn : 8192 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 22) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  refine rungT hn4 (kernDist142 hn4) (δ₂ := 82837 / 10000000) (by norm_num)
    (ratio142 (n₀ := 8192) (by norm_num) hn (by norm_num) (by norm_num))
    (t0 := √6) (z := 6) (Tl := 71355 / 10000000)
    (κl := 405434 / 100000000) (κh := 405436 / 100000000) (Real.sqrt_pos.mpr (by norm_num))
    (Real.sq_sqrt (by norm_num)) (by norm_num) level6.1 (by norm_num) level6.2.1 level6.2.2
    (by norm_num)
    (K := 22) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **Every `n ≥ 10000`, every `1 ≤ k ≤ 23`: the mean of `k` independent exact samples fails
(`|ĝ_k − B| > sd/2`) with probability above `1/100`.** -/
theorem sampleFails144_10000 {n : ℕ} (hn : 10000 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 23) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  refine rungT hn4 (kernDist142 hn4) (δ₂ := 3393 / 500000) (by norm_num)
    (ratio142 (n₀ := 10000) (by norm_num) hn (by norm_num) (by norm_num))
    (t0 := √6) (z := 6) (Tl := 71355 / 10000000)
    (κl := 405434 / 100000000) (κh := 405436 / 100000000) (Real.sqrt_pos.mpr (by norm_num))
    (Real.sq_sqrt (by norm_num)) (by norm_num) level6.1 (by norm_num) level6.2.1 level6.2.2
    (by norm_num)
    (K := 23) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ## The kernel bound of Part 143: every `n ≥ 13225` -/

lemma ratio144_L {n : ℕ} (hn : 13225 ≤ n) :
    (4 / (n : ℝ) * eD143 n) ^ 2 / (4 / (n : ℝ) * (1 - kappa^[6] 0)) ^ 2 ≤ 16073 / 10000000 :=
  ratioE_of (n₀ := 13225) (by norm_num) hn (a := 1027 / 1000) (eD143_nonneg n) (by norm_num)
    (eD143_L hn) (by norm_num)

/-- **Item 2 (`sampleFails144`): the mean of `k` independent exact samples is farther than
`sd/2` from `B` with probability above `1/100`, for every `n ≥ 13225` and every `1 ≤ k ≤ 25`.**
The probability is joint over `(W, A, F)` (the distribution `mlpTriple 2 n` of the Focus) and the
`k` independent uniform inputs `u_j` of the exact samples `F(A(x(u_j)))`, `x(u) = W(u)/|W(u)|`. -/
theorem sampleFails144 {n : ℕ} (hn : 13225 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 25) :
    1 / 100 < ((mlpTriple 2 n).prod (uniK k (2 * n))).real (failSet k) := by
  have hn4 : 4096 ≤ n := by omega
  obtain ⟨hEl, hEu⟩ := exp_258_bounds
  have hz : (0 : ℝ) < 25 / 4 := by norm_num
  have ht2 : (√(25 / 4) : ℝ) ^ 2 = 25 / 4 := Real.sq_sqrt hz.le
  have hE' : Real.exp ((25 / 4 : ℝ) / 2) ≤ 2275990 / 100000 := by
    rw [show ((25 / 4 : ℝ) / 2) = 25 / 8 by norm_num]; exact hEu
  have hE'' : (2275989 : ℝ) / 100000 ≤ Real.exp ((25 / 4 : ℝ) / 2) := by
    rw [show ((25 / 4 : ℝ) / 2) = 25 / 8 by norm_num]; exact hEl
  have hT := tail4_of_mills (z := 25 / 4) (tl := 5 / 2) (E := 2275990 / 100000)
    hz (by norm_num) (by norm_num) (by norm_num) hE'
  obtain ⟨hκl, hκh⟩ := kappa_bounds_of (z := 25 / 4) (tl := 5 / 2)
    (tu := 5 / 2) (El := 2275989 / 100000) (Eu := 2275990 / 100000) hz
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hE'' hE'
  refine rungT hn4 (kernDist143 hn4) (δ₂ := 16073 / 10000000) (by norm_num) (ratio144_L hn)
    (t0 := √(25 / 4)) (z := 25 / 4) (Tl := 61961 / 10000000) (κl := 350565 / 100000000)
    (κh := 350567 / 100000000) (Real.sqrt_pos.mpr hz) ht2 (by norm_num)
    (le_trans (by norm_num) hT) (by norm_num) (le_trans (by norm_num) hκl)
    (le_trans hκh (by norm_num)) (by norm_num) (K := 25) ?_ hk1 hk
  intro j h6 hK
  interval_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

end BstLean.Part144

open BstLean.Part144 in
#print axioms sampleFails144
open BstLean.Part144 in
#print axioms sampleFails144_4096
open BstLean.Part144 in
#print axioms sampleFails144_4500
open BstLean.Part144 in
#print axioms sampleFails144_5500
open BstLean.Part144 in
#print axioms sampleFails144_6500
open BstLean.Part144 in
#print axioms sampleFails144_8192
open BstLean.Part144 in
#print axioms sampleFails144_10000
