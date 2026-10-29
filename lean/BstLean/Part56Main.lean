import BstLean.Part56Defs

/-!
# Part 56, wave 2: the assembly at one law (Theorem RK, §7 of the source)

Specification: `delegations/answers/p56-spec-opus.md` §4.

* `rkg56`: Theorem RK-G from its error part and its floor part:
  `E_Z (B − g)(σZ)² ≤ (δ/(1−δ)) E_Z Var` for `δ < 1`.
* `fail_subset56`: the failure event is in `{V < s EV} ∪ {ε² s EV < (B − g)²}`.
* `fail56`: from Prop T1′ (at `η = etaRK k s ε_lo`) and Prop T2′ (at `p = 1/200`), as hypotheses, there
  is `n₀` such that for `n ≥ n₀` the failure probability is `≤ 1/100`, uniformly in the unit vector
  `v`, in `t ∈ [0, C n]` and in `ε ∈ [ε_lo, ε_hi]`.
* `eval56`: the line program fed by the moment program computes `gLineW` of the surrogate.
* `cost56`: the amortized cost is below the baseline.

This file imports `Part56Defs` only. Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (frob Tens TSymm baseline Pn)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (TF sg)

variable {n d : ℕ}

/-- **Theorem RK-G** (Gaussian proxy) from its two parts: for `δ = √(deltaSq μ d v) < 1`,
`E_Z (B − g)(σZ)² ≤ (δ/(1−δ)) E_Z Var_μ f(σZφ)`. -/
theorem rkg56 (d k : ℕ) (hE : PropRKGErr56 d k) (hF : PropRKGFloor56 d k)
    (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (v : Fin n → ℝ) (hv : UnitV v)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (hδ : Real.sqrt (deltaSq μ d v) < 1) :
    ∫ Z, (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
      Real.sqrt (deltaSq μ d v) / (1 - Real.sqrt (deltaSq μ d v)) * EV56 d μ k f0 T := by
  obtain ⟨-, he⟩ := hE n μ hμ v hv f0 T hT
  have hf := hF n μ hμ v hv f0 T hT
  set δ := Real.sqrt (deltaSq μ d v) with hδdef
  set S := ∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have h1 : 0 < 1 - δ := by linarith
  have hS : S ≤ EV56 d μ k f0 T / (1 - δ) := by
    rw [le_div_iff₀ h1]; linarith
  calc _ ≤ δ * S := he
    _ ≤ δ * (EV56 d μ k f0 T / (1 - δ)) := mul_le_mul_of_nonneg_left hS hδ0
    _ = δ / (1 - δ) * EV56 d μ k f0 T := by ring

/-- The union-bound inclusion of Theorem RK's proof (strict inequalities on both sides). -/
theorem fail_subset56 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (g : (CoefIdxD n d → ℝ) → ℝ) (E ε s : ℝ) :
    {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧
        ε ^ 2 * varFQ μ k f0 T (unitOfD Z) < (BofQ μ k f0 T (unitOfD Z) - g (unitOfD Z)) ^ 2} ⊆
      {Z | Z ≠ 0 ∧ varFQ μ k f0 T (unitOfD Z) < s * E} ∪
      {Z | Z ≠ 0 ∧ ε ^ 2 * s * E < (BofQ μ k f0 T (unitOfD Z) - g (unitOfD Z)) ^ 2} := by
  intro Z ⟨hZ, hf⟩
  by_cases hV : varFQ μ k f0 T (unitOfD Z) < s * E
  · exact Or.inl ⟨hZ, hV⟩
  · refine Or.inr ⟨hZ, ?_⟩
    push Not at hV
    have : ε ^ 2 * (s * E) ≤ ε ^ 2 * varFQ μ k f0 T (unitOfD Z) :=
      mul_le_mul_of_nonneg_left hV (sq_nonneg ε)
    nlinarith

/-- `ofReal a + ofReal b ≤ ofReal c` from real bounds. -/
theorem ofReal_add_le56 {a b A B c : ℝ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B ≤ c) : ENNReal.ofReal a + ENNReal.ofReal b ≤ ENNReal.ofReal c := by
  calc ENNReal.ofReal a + ENNReal.ofReal b ≤ ENNReal.ofReal A + ENNReal.ofReal B :=
        add_le_add (ENNReal.ofReal_le_ofReal ha) (ENNReal.ofReal_le_ofReal hb)
    _ = ENNReal.ofReal (A + B) := (ENNReal.ofReal_add hA hB).symm
    _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal h

/-- `5(k+1)² η² = 5 ε_lo² s / 10⁴` at `η = etaRK k s ε_lo`. -/
theorem etaRK_sq (k : ℕ) (s εlo : ℝ) (hs : 0 ≤ s) :
    5 * ((k : ℝ) + 1) ^ 2 * etaRK k s εlo ^ 2 = 5 * εlo ^ 2 * s / 10000 := by
  unfold etaRK
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_pow, mul_pow, Real.sq_sqrt hs, mul_pow]
  field_simp
  ring

/-- `0 < etaQ e ≤ etaRK k s ε_lo` at `e = eRK k s ε_lo`. -/
theorem etaQ_eRK (k : ℕ) (s εlo : ℝ) (hs : 0 < s) (hlo : 0 < εlo) :
    0 < BstLean.Part43.etaQ (eRK k s εlo) ∧ BstLean.Part43.etaQ (eRK k s εlo) ≤ etaRK k s εlo := by
  have hxi : (0 : ℝ) < BstLean.Part43.xi43 := by unfold BstLean.Part43.xi43; norm_num
  have he : BstLean.Part43.xi43 * eRK k s εlo = etaRK k s εlo := by
    unfold eRK; field_simp
  have hpos : 0 < etaRK k s εlo := by unfold etaRK; positivity
  unfold BstLean.Part43.etaQ
  rw [he]
  exact ⟨lt_min hpos (by norm_num), min_le_left _ _⟩

/-- **The failure bound** of Theorem RK from Props T1′ and T2′. -/
theorem fail56 (d k : ℕ) (C εlo εhi s Cerr C2 : ℝ) (n1 n2 : ℕ) (hlo : 0 < εlo) (hs : 0 < s)
    (h1 : PropT1_56 d k C (eRK k s εlo) Cerr n1) (h2 : PropT2_56 d k C (1 / 200) s C2 n2) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
      ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              gLineW (surrRK n (KRK C n (eRK k s εlo)) t v) k f0 T v (unitOfD Z)) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  set A1 : ℝ := 500 * |C2| with hA1
  set A2 : ℝ := (500 * |Cerr| / (εlo ^ 2 * s)) ^ 2 with hA2
  refine ⟨max (max n1 n2) (max (⌈A1⌉₊ + 1) (⌈A2⌉₊ + 1)),
    fun n hn v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ?_⟩
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : ⌈A1⌉₊ + 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : ⌈A2⌉₊ + 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnA1 : A1 < n := by
    have h := Nat.le_ceil A1
    have : ((⌈A1⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn3
    push_cast at this; linarith
  have hnA2 : A2 < n := by
    have h := Nat.le_ceil A2
    have : ((⌈A2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn4
    push_cast at this; linarith
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hnA1
  have hε : 0 < ε := lt_of_lt_of_le hlo hε1
  have hc : 0 < ε ^ 2 * s := by positivity
  set E := EV56 d (lawRK n t v) k f0 T
  set g := fun M => gLineW (surrRK n (KRK C n (eRK k s εlo)) t v) k f0 T v M
  have hb1 := h1 n hn1 v hv t ht0 ht f0 T hT hTk (ε ^ 2 * s) hc
  have hb2 := h2 n hn2 v hv t ht0 ht f0 T hT hTk
  refine le_trans (measure_mono (fail_subset56 (d := d) (lawRK n t v) k f0 T g E ε s)) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add hb2 hb1) ?_
  -- the real bounds
  have hsq : Real.sqrt n > 500 * |Cerr| / (εlo ^ 2 * s) := by
    have h0 : 0 ≤ 500 * |Cerr| / (εlo ^ 2 * s) := by positivity
    rw [gt_iff_lt, ← Real.sqrt_sq h0]
    exact Real.sqrt_lt_sqrt (by positivity) hnA2
  have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have b1 : 1 / 200 + C2 / n ≤ 1 / 200 + 1 / 500 := by
    have : C2 / n ≤ |C2| / n := div_le_div_of_nonneg_right (le_abs_self _) hnpos.le
    have : |C2| / n ≤ 1 / 500 := by
      rw [div_le_iff₀ hnpos]; linarith
    linarith
  have hε2' : εlo ^ 2 ≤ ε ^ 2 := by nlinarith
  have hq : 5 * ((k : ℝ) + 1) ^ 2 * BstLean.Part43.etaQ (eRK k s εlo) ^ 2 ≤ 5 * εlo ^ 2 * s / 10000 := by
    obtain ⟨hq0, hq1⟩ := etaQ_eRK k s εlo hs hlo
    rw [← etaRK_sq k s εlo hs.le]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0.le hq1 2) (by positivity)
  have b2 : (Cerr / Real.sqrt n + 5 * ((k : ℝ) + 1) ^ 2 * BstLean.Part43.etaQ (eRK k s εlo) ^ 2) /
      (ε ^ 2 * s) ≤ 1 / 500 + 5 / 10000 := by
    refine le_trans (div_le_div_of_nonneg_right (by linarith [hq] : Cerr / Real.sqrt n + 5 * ((k : ℝ) + 1) ^ 2 * BstLean.Part43.etaQ (eRK k s εlo) ^ 2 ≤ Cerr / Real.sqrt n + 5 * εlo ^ 2 * s / 10000) hc.le) ?_
    rw [add_div]
    have e1 : Cerr / Real.sqrt n / (ε ^ 2 * s) ≤ 1 / 500 := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have : 500 * |Cerr| < Real.sqrt n * (εlo ^ 2 * s) := by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < εlo ^ 2 * s)).mp hsq
        linarith
      have h3 : Real.sqrt n * (εlo ^ 2 * s) ≤ Real.sqrt n * (ε ^ 2 * s) := by
        apply mul_le_mul_of_nonneg_left _ hsqpos.le
        exact mul_le_mul_of_nonneg_right hε2' hs.le
      have := le_abs_self Cerr
      nlinarith
    have e2 : 5 * εlo ^ 2 * s / 10000 / (ε ^ 2 * s) ≤ 5 / 10000 := by
      rw [div_le_iff₀ hc]
      nlinarith
    linarith
  exact ofReal_add_le56 b1 b2 (by norm_num) (by norm_num) (by norm_num)

/-- The line program fed by the moment program computes the weight form of the surrogate. -/
theorem eval56 {k : ℕ} (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit) (K : ℕ)
    (hpm : MomSpec56 pm K) (hpg : GSpec56 pg) (t : ℝ) (v : Fin n → ℝ) (ht : 0 ≤ t) (hv : UnitV v)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (M : CoefIdxD n d → ℝ) :
    pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () = gLineW (surrRK n K t v) k f0 T v M := by
  rw [hpg f0 T M v _ hT]
  unfold gLineW
  have : pm.eval (inRK t v) = wRK (surrRK n K t v) d v := funext fun κ => hpm t v ht hv κ
  rw [this]

/-- `0 < ν < 1/2` for `0 < ε_hi² < 91/200`. -/
theorem nuRK_pos (εhi : ℝ) (h : εhi ^ 2 < 91 / 200) : 0 < nuRK εhi := by
  unfold nuRK; linarith

/-- **The cost inequality**: if `cost(pg) ≤ costLine56 < (1 − ν) 0.91 P/ε_hi²` and `ε ≤ ε_hi`, then
for every counter `k′ ≥ k₀`, `cost(pm)/k′ + cost(pg) < 𝔅(ε)`. -/
theorem cost56 (k : ℕ) (hn : 1 ≤ n) (εhi ε : ℝ) (hε : 0 < ε) (hεε : ε ≤ εhi) (hhi : εhi ^ 2 < 91 / 200)
    (cm cg : ℕ) (hcg : (cg : ℝ) ≤ costLine56 n d k)
    (hlt : costLine56 n d k < (1 - nuRK εhi) * (91 / 100) * Pn n d / εhi ^ 2)
    (k' : ℕ) (hk' : k0RK n d cm ε εhi ≤ k') : (cm : ℝ) / k' + cg < baseline n d ε := by
  have hP : 0 < Pn n d := by
    have : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, hn⟩)⟩⟩
    unfold Pn BstLean.Part36.DD
    exact_mod_cast Fintype.card_pos
  have hν := nuRK_pos εhi hhi
  have hν1 : nuRK εhi < 1 := by unfold nuRK; nlinarith [sq_nonneg εhi]
  have hBpos : 0 < baseline n d ε := by
    unfold baseline; exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hk'' : (cm : ℝ) / (nuRK εhi * baseline n d ε) ≤ k' := Nat.ceil_le.mp hk'
  have hmk : (cm : ℝ) / k' ≤ nuRK εhi * baseline n d ε := by
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero]; positivity
    · have hkpos : (0 : ℝ) < k' := by exact_mod_cast h0
      rw [div_le_iff₀ hkpos]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < nuRK εhi * baseline n d ε)).mp hk''
      linarith
  have hεhi : 0 < εhi := lt_of_lt_of_le hε hεε
  have hb1 : (91 / 100) * Pn n d / εhi ^ 2 ≤ baseline n d ε := by
    unfold baseline
    refine le_trans ?_ (le_max_right _ _)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hε.le hεε 2
  have hg : (cg : ℝ) < (1 - nuRK εhi) * baseline n d ε := by
    have : (1 - nuRK εhi) * (91 / 100) * Pn n d / εhi ^ 2 =
        (1 - nuRK εhi) * ((91 / 100) * Pn n d / εhi ^ 2) := by ring
    rw [this] at hlt
    have := mul_le_mul_of_nonneg_left hb1 (by linarith : (0 : ℝ) ≤ 1 - nuRK εhi)
    linarith
  linarith

end BstLean.Part56
