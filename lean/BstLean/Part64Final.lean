import BstLean.Part56Final
import BstLean.Part62SmallBall
import BstLean.Part64Key
import BstLean.Part64T1
import BstLean.Part64T2
import BstLean.Part64Low

/-!
# Part 64: Theorem 1 (the line program, rank one) with an explicit dimension threshold

`Part56Final.part56_general` gives some `n₀`. Here every witness of its proof is a definition:

* `nfail64`: the threshold of `Part56Main.fail56` (`fail64`).
* `ncost64`: the threshold of `Part56Cost.costLine56_lt` (`costLine64_lt`).
* `Kbest h`: a fourth-moment constant at degree `≤ max h 1` (`5⁸` for `h ≤ 4`, `5¹²` for `h ≤ 6`,
  `Part62HyperK.Kexp` otherwise); `tsb64 k = tK (Kbest (2k)) (2k) (1/200)`, `s64 k = tsb64 k / 4`.
* `N56 d k C ε_lo ε_hi`: the explicit `n₀`.
* `part64_general`: the statement of `part56_general` with `n₀ = N56 d k C ε_lo ε_hi` and
  `η = eRK k (s64 k) ε_lo`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount Pn NN)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (lemmaR53 gaussPolar53)
open BstLean.Part56
open BstLean.Part62 (tK tK_pos Kexp Kexp_pos fourth_moment_explicit fourth_moment_5_4 fourth_moment_5_6
  sb_level_of_K)

/-- The threshold of the failure bound: `max (max n₁ n₂) (max (⌈A₁⌉₊+1) (⌈A₂⌉₊+1))`,
`A₁ = 500|C₂|`, `A₂ = (500|C_err|/(ε_lo² s))²`. -/
noncomputable def nfail64 (n1 n2 : ℕ) (C2 Cerr εlo s : ℝ) : ℕ :=
  max (max n1 n2) (max (⌈500 * |C2|⌉₊ + 1) (⌈(500 * |Cerr| / (εlo ^ 2 * s)) ^ 2⌉₊ + 1))

/-- **The failure bound** of Theorem RK from Props T1′ and T2′, with the explicit threshold. -/
theorem fail64 (d k : ℕ) (C εlo εhi s Cerr C2 : ℝ) (n1 n2 : ℕ) (hlo : 0 < εlo) (hs : 0 < s)
    (h1 : PropT1_56 d k C (eRK k s εlo) Cerr n1) (h2 : PropT2_56 d k C (1 / 200) s C2 n2) :
    ∀ n : ℕ, nfail64 n1 n2 C2 Cerr εlo s ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
      ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              gLineW (surrRK n (KRK C n (eRK k s εlo)) t v) k f0 T v (unitOfD Z)) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  set A1 : ℝ := 500 * |C2| with hA1
  set A2 : ℝ := (500 * |Cerr| / (εlo ^ 2 * s)) ^ 2 with hA2
  unfold nfail64
  rw [← hA1, ← hA2]
  intro n hn v hv t ht0 ht ε hε1 hε2 f0 T hT hTk
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


/-- The threshold of the cost bound: `⌈2(d+1)/γ⌉₊ + ⌈2 · d! · B · 2^k/γ⌉₊ + 1`,
`γ = 91/(200 ε_hi²) − 1`, `B = 4(k+2)³(d+1)^k`. -/
noncomputable def ncost64 (d k : ℕ) (εhi : ℝ) : ℕ :=
  ⌈2 * ((d : ℝ) + 1) / (91 / (200 * εhi ^ 2) - 1)⌉₊ +
    ⌈2 * (d.factorial : ℝ) * (4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k) * 2 ^ k /
      (91 / (200 * εhi ^ 2) - 1)⌉₊ + 1

/-- **The cost bound** with the explicit threshold `ncost64`. -/
theorem costLine64_lt (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (εhi : ℝ) (h0 : 0 < εhi)
    (h : εhi ^ 2 < 91 / 200) :
    ∀ n : ℕ, ncost64 d k εhi ≤ n →
      costLine56 n d k < (1 - nuRK εhi) * (91 / 100) * Pn n d / εhi ^ 2 := by
  set e := εhi ^ 2 with he_def
  have he : 0 < e := by positivity
  set γ : ℝ := 91 / (200 * e) - 1 with hγdef
  have hγ : 0 < γ := by
    rw [hγdef, sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have hrhs : ∀ P : ℝ, (1 - nuRK εhi) * (91 / 100) * P / e = (2 + γ) * P := by
    intro P; unfold nuRK; rw [← he_def, hγdef]; field_simp; ring
  set B : ℝ := 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k with hB
  set F : ℝ := (d.factorial : ℝ) with hF
  have hF0 : 0 < F := by positivity
  have hB0 : 0 ≤ B := by positivity
  unfold ncost64
  rw [← he_def, ← hγdef, ← hB, ← hF]
  intro n hn
  have hn1 : (2 * ((d : ℝ) + 1) / γ) < n := by
    have := Nat.le_ceil (2 * ((d : ℝ) + 1) / γ)
    have h' : ((⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h'
    have : (0 : ℝ) ≤ ⌈2 * F * B * 2 ^ k / γ⌉₊ := Nat.cast_nonneg _
    linarith
  have hn2 : (2 * F * B * 2 ^ k / γ) < n := by
    have := Nat.le_ceil (2 * F * B * 2 ^ k / γ)
    have h' : ((⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h'
    have : (0 : ℝ) ≤ ⌈2 * ((d : ℝ) + 1) / γ⌉₊ := Nat.cast_nonneg _
    linarith
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn1
  have hn1' : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by
      have h' : ((⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h'
      have : (0 : ℝ) ≤ ⌈2 * ((d : ℝ) + 1) / γ⌉₊ := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ⌈2 * F * B * 2 ^ k / γ⌉₊ := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
  rw [hrhs, Pn_eq56]
  unfold costLine56
  rw [Pn_eq56]
  set N := NN n d
  have hN1 := NN_ge_one56 n d
  have hNd := NN_ge56 n d hn1'
  -- (a) (d+1) N ≤ (γ/2) n N
  have ha : ((d : ℝ) + 1) * N ≤ γ / 2 * n * N := by
    have : (d : ℝ) + 1 ≤ γ / 2 * n := by
      rw [div_lt_iff₀ hγ] at hn1; nlinarith
    nlinarith
  -- (b) B (n+1)^k < (γ/2) n N
  have hpow1 : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hpow2 : (n : ℝ) ^ k ≤ (n : ℝ) ^ d := pow_le_pow_right₀ hnr hkd
  have hNk : (n : ℝ) ^ k / F ≤ N := le_trans (div_le_div_of_nonneg_right hpow2 hF0.le) hNd
  have hb : B * ((n : ℝ) + 1) ^ k < γ / 2 * n * N := by
    have hnk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    have step1 : B * ((n : ℝ) + 1) ^ k ≤ B * 2 ^ k * (n : ℝ) ^ k := by
      have := mul_le_mul_of_nonneg_left hpow1 hB0
      calc B * ((n : ℝ) + 1) ^ k ≤ B * (2 ^ k * (n : ℝ) ^ k) := this
        _ = B * 2 ^ k * (n : ℝ) ^ k := by ring
    have step2 : B * 2 ^ k * (n : ℝ) ^ k < γ / 2 * n * ((n : ℝ) ^ k / F) := by
      rw [div_lt_iff₀ hγ] at hn2
      have : γ / 2 * n * ((n : ℝ) ^ k / F) = (γ * n) * (n : ℝ) ^ k / (2 * F) := by
        field_simp
      rw [this, lt_div_iff₀ (by positivity)]
      nlinarith
    have step3 : γ / 2 * n * ((n : ℝ) ^ k / F) ≤ γ / 2 * n * N :=
      mul_le_mul_of_nonneg_left hNk (by positivity)
    linarith
  have : 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k = B * ((n : ℝ) + 1) ^ k := by
    rw [hB]
  rw [this]
  nlinarith


/-- A fourth-moment constant at degree `≤ max h 1`: `5⁸` (`h ≤ 4`), `5¹²` (`h ≤ 6`), `Kexp (max h 1)`. -/
noncomputable def Kbest (h : ℕ) : ℝ :=
  if h ≤ 4 then 5 ^ 8 else if h ≤ 6 then 5 ^ 12 else Kexp (max h 1)

lemma Kbest_pos (h : ℕ) : 0 < Kbest h := by
  unfold Kbest; split_ifs
  · norm_num
  · norm_num
  · exact Kexp_pos _

theorem fourth_moment_best (h : ℕ) : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    P.totalDegree ≤ max h 1 →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        Kbest h * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  intro ι _ P hP
  unfold Kbest
  split_ifs with h4 h6
  · exact fourth_moment_5_4 ι P (hP.trans (max_le h4 (by norm_num)))
  · exact fourth_moment_5_6 ι P (hP.trans (max_le h6 (by norm_num)))
  · exact fourth_moment_explicit (max h 1) ι P hP

/-- The explicit small-ball level at degree `2k`, `p = 1/200`. -/
noncomputable def tsb64 (k : ℕ) : ℝ := tK (Kbest (2 * k)) (2 * k) (1 / 200)

/-- `s = t_sb/4`. -/
noncomputable def s64 (k : ℕ) : ℝ := tsb64 k / 4

lemma tsb64_pos (k : ℕ) : 0 < tsb64 k := tK_pos _ (Kbest_pos _) _ _ (by norm_num)

lemma sb_level64 (k : ℕ) : SBLevel (2 * k) (1 / 200) (tsb64 k) :=
  sb_level_of_K (2 * k) (Kbest (2 * k)) (Kbest_pos _) (fourth_moment_best (2 * k)) (1 / 200) (by norm_num)

/-- The explicit Prop D constant of Theorem 1: `CD64 d (CK64 d)`. -/
noncomputable def CDT1 (d : ℕ) : ℝ := CD64 d (CK64 d)

/-- The explicit failure threshold of Theorem 1. -/
noncomputable def NF56 (d k : ℕ) (C εlo : ℝ) : ℕ :=
  nfail64 (n1T1_64 (CDT1 d)) (n2T2_64 (CDT1 d) (nL64 C)) (C2T2_64 d k (tsb64 k) (cL64 d k C))
    (Cerr64 k (CDT1 d)) εlo (s64 k)

/-- **The explicit `n₀` of Theorem 1**: `max (max (NF56 d k C ε_lo) (ncost64 d k ε_hi)) 100`. -/
noncomputable def N56 (d k : ℕ) (C εlo εhi : ℝ) : ℕ :=
  max (max (NF56 d k C εlo) (ncost64 d k εhi)) 100

/-- **The failure bound** of Theorem RK with the explicit threshold `NF56`. -/
theorem part64_fail (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (C εlo εhi : ℝ) (hlo : 0 < εlo) :
    ∀ n : ℕ, NF56 d k C εlo ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
      ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              gLineW (surrRK n (KRK C n (eRK k (s64 k) εlo)) t v) k f0 T v (unitOfD Z)) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  have hd : 1 ≤ d := by omega
  have hk1 : 1 ≤ k := by omega
  have htsb_pos := tsb64_pos k
  have hSB := sb_level64 k
  have hs0 : 0 < s64 k := by unfold s64; positivity
  have he0 : 0 < eRK k (s64 k) εlo := by
    unfold eRK etaRK BstLean.Part43.xi43; positivity
  have hK := keyLemma64 d
  have hD := (propD64_of d hd (CK64 d) hK).2
  have hMC := lemmaMC56
  have hW := propWeights56 d k
  have hSp := propSplit56 d
  have hO := propOrth56 d k hSp
  have hE := propRKGErr56_of d k hMC hSp
  have hF := propRKGFloor56_of d k hE hO hSp
  have hS := propSurr56_of d k C (eRK k (s64 k) εlo) he0 hO hW
  have h1 := propT1_64_of d k hd hk1 C (eRK k (s64 k) εlo) (CDT1 d) (lemmaR53 k) gaussPolar53
    hW hE hF hD hS
  have hL := propLow64 d k hk1 hkd C
  have h2 := propT2_64_of d k hk1 hkd C (1 / 200) (tsb64 k) hSB htsb_pos gaussPolar53 hE hF
    (CDT1 d) hD (cL64 d k C) (nL64 C) (cL64_pos d k C) hL
  exact fail64 d k C εlo εhi (s64 k) _ _ _ _ hlo hs0 h1 h2

/-- **Theorem 1 (Theorem RK) with an explicit threshold**: for `2 ≤ d_f = k ≤ d_M = d`,
`0 < ε_lo ≤ ε_hi`, `ε_hi² < 91/200` and every `C`, with `η = eRK k (s64 k) ε_lo` and
`n₀ = N56 d k C ε_lo ε_hi`, the conclusion of `Part56.part56_general` holds for every `n ≥ n₀`. -/
theorem part64_general (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (C εlo εhi : ℝ) (hlo : 0 < εlo)
    (hlh : εlo ≤ εhi) (hhi : εhi ^ 2 < 91 / 200) :
    0 < eRK k (s64 k) εlo ∧ 100 ≤ N56 d k C εlo εhi ∧ ∀ n : ℕ, N56 d k C εlo εhi ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpec56 pm (KRK C n (eRK k (s64 k) εlo)) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n d k (KRK C n (eRK k (s64 k) εlo)) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
        ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
        ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n d pm.cost ε εhi ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n d ε := by
  set s := s64 k with hsdef
  have hfail := part64_fail k d hk hkd C εlo εhi hlo
  have hεhi : 0 < εhi := lt_of_lt_of_le hlo hlh
  have hc := costLine64_lt d k (by omega) hkd εhi hεhi hhi
  have hs0 : 0 < s := by rw [hsdef]; unfold s64; have := tsb64_pos k; positivity
  have hη0 : 0 < eRK k s εlo := by unfold eRK etaRK BstLean.Part43.xi43; positivity
  refine ⟨hη0, le_max_right _ _, fun n hn => ?_⟩
  unfold N56 at hn
  have hnf : NF56 d k C εlo ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : ncost64 d k εhi ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn100 : 100 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n d k (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := momProg56_exists n d k (KRK C n (eRK k s εlo)) (by omega)
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc, fun v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have heval : ∀ M : CoefIdxD n d → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
          gLineW (surrRK n (KRK C n (eRK k s εlo)) t v) k f0 T v M :=
      fun M => eval56 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
    simp only [heval]
    exact hfail n hnf v hv t ht0 ht ε hε1 hε2 f0 T hT hTk
  · intro k' hk'
    exact cost56 k (by omega) εhi ε (lt_of_lt_of_le hlo hε1) hε2 hhi pm.cost pg.cost hpgc (hc n hnc) k' hk'

end BstLean.Part64
