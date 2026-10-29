import BstLean.Part64Final
import BstLean.Part66Defs

/-!
# Part 66: Theorem 1 with the threshold as a function of the small-ball level

Copy of `Part64Final.NF56`, `N56`, `part64_fail`, `part64_general` with the level `tsb64 k`
replaced by a parameter `t` (`s = t/4`), and the hypothesis `SBLevel (2k) (1/200) t`.

* `NF56L d k C εlo t`, `N56L d k C εlo εhi t`: the thresholds at level `t`.
* `part66T1_general`: the conclusion of `part64_general` from any level `t > 0`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part66

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (lemmaR53 gaussPolar53)
open BstLean.Part56
open BstLean.Part64

/-- The failure threshold of Theorem 1 at small-ball level `t` (`s = t/4`). -/
noncomputable def NF56L (d k : ℕ) (C εlo t : ℝ) : ℕ :=
  nfail64 (n1T1_64 (CDT1 d)) (n2T2_64 (CDT1 d) (nL64 C)) (C2T2_64 d k t (cL64 d k C))
    (Cerr64 k (CDT1 d)) εlo (t / 4)

/-- The explicit `n₀` of Theorem 1 at small-ball level `t`. -/
noncomputable def N56L (d k : ℕ) (C εlo εhi t : ℝ) : ℕ :=
  max (max (NF56L d k C εlo t) (ncost64 d k εhi)) 100

/-- **The failure bound** of Theorem RK at any small-ball level `t`. -/
theorem part66T1_fail (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (C εlo εhi : ℝ) (hlo : 0 < εlo)
    (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * k) (1 / 200) t) :
    ∀ n : ℕ, NF56L d k C εlo t ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t' : ℝ, 0 ≤ t' → t' ≤ C * n →
      ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t' v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t' v) k f0 T (unitOfD Z) -
              gLineW (surrRK n (KRK C n (eRK k (t / 4) εlo)) t' v) k f0 T v (unitOfD Z)) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  have hd : 1 ≤ d := by omega
  have hk1 : 1 ≤ k := by omega
  have hs0 : 0 < t / 4 := by positivity
  have he0 : 0 < eRK k (t / 4) εlo := by
    unfold eRK etaRK BstLean.Part43.xi43; positivity
  have hK := keyLemma64 d
  have hD := (propD64_of d hd (CK64 d) hK).2
  have hMC := lemmaMC56
  have hW := propWeights56 d k
  have hSp := propSplit56 d
  have hO := propOrth56 d k hSp
  have hE := propRKGErr56_of d k hMC hSp
  have hF := propRKGFloor56_of d k hE hO hSp
  have hS := propSurr56_of d k C (eRK k (t / 4) εlo) he0 hO hW
  have h1 := propT1_64_of d k hd hk1 C (eRK k (t / 4) εlo) (CDT1 d) (lemmaR53 k) gaussPolar53
    hW hE hF hD hS
  have hL := propLow64 d k hk1 hkd C
  have h2 := propT2_64_of d k hk1 hkd C (1 / 200) t hSB ht gaussPolar53 hE hF
    (CDT1 d) hD (cL64 d k C) (nL64 C) (cL64_pos d k C) hL
  exact fail64 d k C εlo εhi (t / 4) _ _ _ _ hlo hs0 h1 h2

/-- **Theorem 1 (Theorem RK) from any small-ball level `t`**: for `2 ≤ k ≤ d`,
`0 < ε_lo ≤ ε_hi`, `ε_hi² < 91/200`, every `C`, and `t > 0` with `SBLevel (2k) (1/200) t`,
with `η = eRK k (t/4) ε_lo` and `n₀ = N56L d k C ε_lo ε_hi t`, the conclusion of
`Part64.part64_general` holds for every `n ≥ n₀`. -/
theorem part66T1_general (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (C εlo εhi : ℝ) (hlo : 0 < εlo)
    (hlh : εlo ≤ εhi) (hhi : εhi ^ 2 < 91 / 200)
    (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * k) (1 / 200) t) :
    0 < eRK k (t / 4) εlo ∧ 100 ≤ N56L d k C εlo εhi t ∧ ∀ n : ℕ, N56L d k C εlo εhi t ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpec56 pm (KRK C n (eRK k (t / 4) εlo)) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n d k (KRK C n (eRK k (t / 4) εlo)) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t' : ℝ, 0 ≤ t' → t' ≤ C * n →
        ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
        ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t' v) k f0 T (unitOfD Z) <
              (BofQ (lawRK n t' v) k f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t' v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n d pm.cost ε εhi ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n d ε := by
  set s := t / 4 with hsdef
  have hfail := part66T1_fail k d hk hkd C εlo εhi hlo t ht hSB
  have hεhi : 0 < εhi := lt_of_lt_of_le hlo hlh
  have hc := costLine64_lt d k (by omega) hkd εhi hεhi hhi
  have hs0 : 0 < s := by positivity
  have hη0 : 0 < eRK k s εlo := by unfold eRK etaRK BstLean.Part43.xi43; positivity
  refine ⟨hη0, le_max_right _ _, fun n hn => ?_⟩
  unfold N56L at hn
  have hnf : NF56L d k C εlo t ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : ncost64 d k εhi ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n d k (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := momProg56_exists n d k (KRK C n (eRK k s εlo)) (by omega)
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc, fun v hv t' ht0 ht' ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have heval : ∀ M : CoefIdxD n d → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t' v))) () =
          gLineW (surrRK n (KRK C n (eRK k s εlo)) t' v) k f0 T v M :=
      fun M => eval56 pm pg _ hpms hpgs t' v ht0 hv f0 T hT M
    simp only [heval]
    exact hfail n hnf v hv t' ht0 ht' ε hε1 hε2 f0 T hT hTk
  · intro k' hk'
    exact cost56 k (by omega) εhi ε (lt_of_lt_of_le hlo hε1) hε2 hhi pm.cost pg.cost hpgc (hc n hnc) k' hk'

end BstLean.Part66
