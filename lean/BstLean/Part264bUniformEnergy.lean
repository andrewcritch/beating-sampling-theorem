import BstLean.Part264FiniteCentre
import BstLean.Part264EnergyLower
import BstLean.Part253EnergyUpper
namespace BstLean.Part264b
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem uniform_energy_upper_from_kappas {n : ℕ} (hn : 12227 ≤ n) {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12227 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12227 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12227 + 0.008646 / 110.566721) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (12227 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / 12227 := by gcongr
      linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    have h : (2 : ℝ) * √12 / n ≤ 2 * 3.464102 / 12227 := by gcongr
    linarith
  have hm0 : 0 ≤ meanRoot n q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := BstLean.Part264.gMinus_lower (by omega : 12225 ≤ n)
  have hg0 : 0 < gMinus n := by linarith
  have hratio : energyRatio n (gMinus n) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    gcongr
  have hr0 : 0 ≤ energyRatio n (gMinus n) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0.le
  have hQ20 : 0 ≤ Q2 := hr0.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio n (gMinus n) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio n (gMinus n) q)
    (by linarith : energyRatio n (gMinus n) q ≤ 1)).1
  have hgp := BstLean.Part264.gPlus_upper (by omega : 12225 ≤ n)
  have hgp0 : 0 ≤ BstLean.Part211.gPlus n := le_trans zero_le_one (BstLean.Part264.gPlus_lower n)
  have ht : √(BstLean.Part211.gPlus n * kappa (energyRatio n (gMinus n) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 (by norm_num)).trans hTsq
  have ht2 : √(12 * BstLean.Part211.gPlus n) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (110.566721 : ℝ) ≤ √n := le_sqrt_of_sq_le (by nlinarith [hnlo])
  have hf := BstLean.Part264.finite_centre_upper (by omega : 12225 ≤ n)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  gcongr



theorem uniformEnergy10 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (528019577737/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1752748513378199/2500000000000000) := by
  have hk1 : kappa q ≤ 0.627908763869 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528019577737 : ℝ)) (s := (0.849232197651 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629930119235 : ℝ) ≤ 0.699124706805 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629930119235 : ℝ)) (Q := (0.629930119235 : ℝ))
      (s := (0.776651817021 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792664932316 : ℝ)) (R := (0.793231563870 : ℝ)) (Q2 := (0.629930119235 : ℝ)) (T := (0.836610638479 : ℝ))
    (B := ((1752748513378199/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy11 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (526821535511/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (7005160765931617/10000000000000000) := by
  have hk1 : kappa q ≤ 0.627096448803 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526821535511 : ℝ)) (s := (0.849975923025 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.629116301126 : ℝ) ≤ 0.698538800138 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629116301126 : ℝ)) (Q := (0.629116301126 : ℝ))
      (s := (0.777311185857 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.792152371617 : ℝ)) (R := (0.792719003171 : ℝ)) (Q2 := (0.629116301126 : ℝ)) (T := (0.836260001112 : ℝ))
    (B := ((7005160765931617/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy12 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (105124698657/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1399866809028941/2000000000000000) := by
  have hk1 : kappa q ≤ 0.626284690960 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525623493285 : ℝ)) (s := (0.850717311043 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.628303040893 : ℝ) ≤ 0.697953581956 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628303040893 : ℝ)) (Q := (0.628303040893 : ℝ))
      (s := (0.777968693975 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791639830993 : ℝ)) (R := (0.792206462547 : ℝ)) (Q2 := (0.628303040893 : ℝ)) (T := (0.835909628949 : ℝ))
    (B := ((1399866809028941/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy13 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (262212725529/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6993513880135863/10000000000000000) := by
  have hk1 : kappa q ≤ 0.625473489669 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524425451058 : ℝ)) (s := (0.851456367810 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.627490337867 : ℝ) ≤ 0.697369050947 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627490337867 : ℝ)) (Q := (0.627490337867 : ℝ))
      (s := (0.778624348376 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.791127310061 : ℝ)) (R := (0.791693941615 : ℝ)) (Q2 := (0.627490337867 : ℝ)) (T := (0.835559521537 : ℝ))
    (B := ((6993513880135863/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy14 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (8175428263/15625000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (698770025993281/1000000000000000) := by
  have hk1 : kappa q ≤ 0.624662844268 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523227408832 : ℝ)) (s := (0.852193099390 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.626678191382 : ℝ) ≤ 0.696785205799 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626678191382 : ℝ)) (Q := (0.626678191382 : ℝ))
      (s := (0.779278156018 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790614808439 : ℝ)) (R := (0.791181439993 : ℝ)) (Q2 := (0.626678191382 : ℝ)) (T := (0.835209678422 : ℝ))
    (B := ((698770025993281/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy15 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (261014683303/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (436368323350431/625000000000000) := by
  have hk1 : kappa q ≤ 0.623852754093 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522029366606 : ℝ)) (s := (0.852927511810 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625866600775 : ℝ) ≤ 0.696202045207 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625866600775 : ℝ)) (Q := (0.625866600775 : ℝ))
      (s := (0.779930123816 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.790102325745 : ℝ)) (R := (0.790668957299 : ℝ)) (Q2 := (0.625866600775 : ℝ)) (T := (0.834860099156 : ℝ))
    (B := ((436368323350431/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy16 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (520831324379/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6976092610272833/10000000000000000) := by
  have hk1 : kappa q ≤ 0.623043218483 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520831324379 : ℝ)) (s := (0.853659611055 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.625055565385 : ℝ) ≤ 0.695619567867 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625055565385 : ℝ)) (Q := (0.625055565385 : ℝ))
      (s := (0.780580258642 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789589861598 : ℝ)) (R := (0.790156493152 : ℝ)) (Q2 := (0.625055565385 : ℝ)) (T := (0.834510783287 : ℝ))
    (B := ((6976092610272833/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy17 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (519633282153/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6970298559088419/10000000000000000) := by
  have hk1 : kappa q ≤ 0.622234236785 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519633282153 : ℝ)) (s := (0.854389403071 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.624245084554 : ℝ) ≤ 0.695037772482 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624245084554 : ℝ)) (Q := (0.624245084554 : ℝ))
      (s := (0.781228567329 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.789077415619 : ℝ)) (R := (0.789644047173 : ℝ)) (Q2 := (0.624245084554 : ℝ)) (T := (0.834161730367 : ℝ))
    (B := ((6970298559088419/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy18 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (518435239927/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6964511009254271/10000000000000000) := by
  have hk1 : kappa q ≤ 0.621425808344 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518435239927 : ℝ)) (s := (0.855116893765 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.623435157628 : ℝ) ≤ 0.694456657757 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623435157628 : ℝ)) (Q := (0.623435157628 : ℝ))
      (s := (0.781875056665 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788564987429 : ℝ)) (R := (0.789131618983 : ℝ)) (Q2 := (0.623435157628 : ℝ)) (T := (0.833812939950 : ℝ))
    (B := ((6964511009254271/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy19 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (5172371977/10000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1391745990002711/2000000000000000) := by
  have hk1 : kappa q ≤ 0.620617932511 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517237197700 : ℝ)) (s := (0.855842089007 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.622625783957 : ℝ) ≤ 0.693876222403 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622625783957 : ℝ)) (Q := (0.622625783957 : ℝ))
      (s := (0.782519733395 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.788052576651 : ℝ)) (R := (0.788619208205 : ℝ)) (Q2 := (0.622625783957 : ℝ)) (T := (0.833464411590 : ℝ))
    (B := ((1391745990002711/2000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy20 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (258019577737/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6952955370651723/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619810608638 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516039155474 : ℝ)) (s := (0.856564994626 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621816962892 : ℝ) ≤ 0.693296465133 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621816962892 : ℝ)) (Q := (0.621816962892 : ℝ))
      (s := (0.783162604228 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787540182907 : ℝ)) (R := (0.788106814461 : ℝ)) (Q2 := (0.621816962892 : ℝ)) (T := (0.833116144844 : ℝ))
    (B := ((6952955370651723/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy21 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (16088784789/31250000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6947187260496249/10000000000000000) := by
  have hk1 : kappa q ≤ 0.619003836083 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514841113248 : ℝ)) (s := (0.857285616414 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.621008693789 : ℝ) ≤ 0.692717384665 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621008693789 : ℝ)) (Q := (0.621008693789 : ℝ))
      (s := (0.783803675827 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.787027805823 : ℝ)) (R := (0.787594437377 : ℝ)) (Q2 := (0.621008693789 : ℝ)) (T := (0.832768139269 : ℝ))
    (B := ((6947187260496249/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy22 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (513643071021/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6941425608916369/10000000000000000) := by
  have hk1 : kappa q ≤ 0.618197614204 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513643071021 : ℝ)) (s := (0.858003960127 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.620200976005 : ℝ) ≤ 0.692138979721 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620200976005 : ℝ)) (Q := (0.620200976005 : ℝ))
      (s := (0.784442954818 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786515445023 : ℝ)) (R := (0.787082076577 : ℝ)) (Q2 := (0.620200976005 : ℝ)) (T := (0.832420394425 : ℝ))
    (B := ((6941425608916369/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy23 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (102489005759/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6935670405322821/10000000000000000) := by
  have hk1 : kappa q ≤ 0.617391942364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512445028795 : ℝ)) (s := (0.858720031479 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.619393808901 : ℝ) ≤ 0.691561249028 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619393808901 : ℝ)) (Q := (0.619393808901 : ℝ))
      (s := (0.785080447786 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.786003100133 : ℝ)) (R := (0.786569731687 : ℝ)) (Q2 := (0.619393808901 : ℝ)) (T := (0.832072909871 : ℝ))
    (B := ((6935670405322821/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy24 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (511246986569/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (866240204895949/1250000000000000) := by
  have hk1 : kappa q ≤ 0.616586819930 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511246986569 : ℝ)) (s := (0.859433836153 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.618587191846 : ℝ) ≤ 0.690984191319 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618587191846 : ℝ)) (Q := (0.618587191846 : ℝ))
      (s := (0.785716161273 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.785490770783 : ℝ)) (R := (0.786057402337 : ℝ)) (Q2 := (0.618587191846 : ℝ)) (T := (0.831725685173 : ℝ))
    (B := ((866240204895949/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy25 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (510048944343/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (432761206246479/625000000000000) := by
  have hk1 : kappa q ≤ 0.615782246269 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510048944343 : ℝ)) (s := (0.860145379791 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.617781124203 : ℝ) ≤ 0.690407805326 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617781124203 : ℝ)) (Q := (0.617781124203 : ℝ))
      (s := (0.786350101786 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784978456599 : ℝ)) (R := (0.785545088153 : ℝ)) (Q2 := (0.617781124203 : ℝ)) (T := (0.831378719891 : ℝ))
    (B := ((432761206246479/625000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy26 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (127212725529/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6918443377184757/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614978220754 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508850902116 : ℝ)) (s := (0.860854668000 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616975605344 : ℝ) ≤ 0.689832089788 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616975605344 : ℝ)) (Q := (0.616975605344 : ℝ))
      (s := (0.786982275792 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.784466157211 : ℝ)) (R := (0.785032788765 : ℝ)) (Q2 := (0.616975605344 : ℝ)) (T := (0.831032013592 : ℝ))
    (B := ((6918443377184757/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy27 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (50765285989/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6912713860465089/10000000000000000) := by
  have hk1 : kappa q ≤ 0.614174742760 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507652859890 : ℝ)) (s := (0.861561706349 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.616170634644 : ℝ) ≤ 0.689257043450 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616170634644 : ℝ)) (Q := (0.616170634644 : ℝ))
      (s := (0.787612689717 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783953872250 : ℝ)) (R := (0.784520503804 : ℝ)) (Q2 := (0.616170634644 : ℝ)) (T := (0.830685565844 : ℝ))
    (B := ((6912713860465089/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy28 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (3956678263/7812500000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (86337384242489/125000000000000) := by
  have hk1 : kappa q ≤ 0.613371811666 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506454817664 : ℝ)) (s := (0.862266500373 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.615366211480 : ℝ) ≤ 0.688682665059 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615366211480 : ℝ)) (Q := (0.615366211480 : ℝ))
      (s := (0.788241349949 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.783441601347 : ℝ)) (R := (0.784008232901 : ℝ)) (Q2 := (0.615366211480 : ℝ)) (T := (0.830339376214 : ℝ))
    (B := ((86337384242489/125000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy29 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (505256775437/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3450637001820657/5000000000000000) := by
  have hk1 : kappa q ≤ 0.612569426852 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505256775437 : ℝ)) (s := (0.862969055573 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.614562335232 : ℝ) ≤ 0.688108953366 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614562335232 : ℝ)) (Q := (0.614562335232 : ℝ))
      (s := (0.788868262839 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782929344135 : ℝ)) (R := (0.783495975689 : ℝ)) (Q2 := (0.614562335232 : ℝ)) (T := (0.829993444273 : ℝ))
    (B := ((3450637001820657/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy30 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (504058733211/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6895563642885889/10000000000000000) := by
  have hk1 : kappa q ≤ 0.611767587705 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504058733211 : ℝ)) (s := (0.863669377409 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.613759005284 : ℝ) ≤ 0.687535907129 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613759005284 : ℝ)) (Q := (0.613759005284 : ℝ))
      (s := (0.789493434699 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.782417100248 : ℝ)) (R := (0.782983731802 : ℝ)) (Q2 := (0.613759005284 : ℝ)) (T := (0.829647769593 : ℝ))
    (B := ((6895563642885889/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy31 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (100572138197/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (861232455858323/1250000000000000) := by
  have hk1 : kappa q ≤ 0.610966293612 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502860690985 : ℝ)) (s := (0.864367471312 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612956221022 : ℝ) ≤ 0.686963525106 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612956221022 : ℝ)) (Q := (0.612956221022 : ℝ))
      (s := (0.790116871805 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781904869320 : ℝ)) (R := (0.782471500874 : ℝ)) (Q2 := (0.612956221022 : ℝ)) (T := (0.829302351747 : ℝ))
    (B := ((861232455858323/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy32 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (250831324379/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6884162005356413/10000000000000000) := by
  have hk1 : kappa q ≤ 0.610165543963 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501662648758 : ℝ)) (s := (0.865063342676 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.612153981839 : ℝ) ≤ 0.686391806065 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612153981839 : ℝ)) (Q := (0.612153981839 : ℝ))
      (s := (0.790738580391 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.781392650988 : ℝ)) (R := (0.781959282542 : ℝ)) (Q2 := (0.612153981839 : ℝ)) (T := (0.828957190311 : ℝ))
    (B := ((6884162005356413/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy33 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (125116151633/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3439235354083717/5000000000000000) := by
  have hk1 : kappa q ≤ 0.609365338153 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500464606532 : ℝ)) (s := (0.865756996859 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.611352287124 : ℝ) ≤ 0.685820748772 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611352287124 : ℝ)) (Q := (0.611352287124 : ℝ))
      (s := (0.791358566662 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780880444888 : ℝ)) (R := (0.781447076442 : ℝ)) (Q2 := (0.611352287124 : ℝ)) (T := (0.828612284860 : ℝ))
    (B := ((3439235354083717/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy34 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (249633282153/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1718196436287627/2500000000000000) := by
  have hk1 : kappa q ≤ 0.608565675580 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499266564306 : ℝ)) (s := (0.866448439185 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.610551136276 : ℝ) ≤ 0.685250352002 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610551136276 : ℝ)) (Q := (0.610551136276 : ℝ))
      (s := (0.791976836778 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.780368250658 : ℝ)) (R := (0.780934882212 : ℝ)) (Q2 := (0.610551136276 : ℝ)) (T := (0.828267634975 : ℝ))
    (B := ((1718196436287627/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy35 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (498068522079/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (274684284247803/400000000000000) := by
  have hk1 : kappa q ≤ 0.607766555644 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498068522079 : ℝ)) (s := (0.867137674948 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.609750528694 : ℝ) ≤ 0.684680614533 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609750528694 : ℝ)) (Q := (0.609750528694 : ℝ))
      (s := (0.792593396868 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779856067938 : ℝ)) (R := (0.780422699492 : ℝ)) (Q2 := (0.609750528694 : ℝ)) (T := (0.827923240235 : ℝ))
    (B := ((274684284247803/400000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy36 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (496870479853/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3430717390614457/5000000000000000) := by
  have hk1 : kappa q ≤ 0.606967977749 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496870479853 : ℝ)) (s := (0.867824709404 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608950463781 : ℝ) ≤ 0.684111535146 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608950463781 : ℝ)) (Q := (0.608950463781 : ℝ))
      (s := (0.793208253022 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.779343896367 : ℝ)) (R := (0.779910527921 : ℝ)) (Q2 := (0.608950463781 : ℝ)) (T := (0.827579100221 : ℝ))
    (B := ((3430717390614457/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy37 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (495672437627/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6855768760217921/10000000000000000) := by
  have hk1 : kappa q ≤ 0.606169941301 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495672437627 : ℝ)) (s := (0.868509547776 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.608150940940 : ℝ) ≤ 0.683543112625 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608150940940 : ℝ)) (Q := (0.608150940940 : ℝ))
      (s := (0.793821411298 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778831735586 : ℝ)) (R := (0.779398367140 : ℝ)) (Q2 := (0.608150940940 : ℝ)) (T := (0.827235214516 : ℝ))
    (B := ((6855768760217921/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy38 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (2472371977/5000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6850109033165879/10000000000000000) := by
  have hk1 : kappa q ≤ 0.605372445711 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494474395400 : ℝ)) (s := (0.869192195256 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.607351959584 : ℝ) ≤ 0.682975345765 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607351959584 : ℝ)) (Q := (0.607351959584 : ℝ))
      (s := (0.794432877712 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.778319585239 : ℝ)) (R := (0.778886216793 : ℝ)) (Q2 := (0.607351959584 : ℝ)) (T := (0.826891582708 : ℝ))
    (B := ((6850109033165879/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy39 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (246638176587/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (855556948764279/1250000000000000) := by
  have hk1 : kappa q ≤ 0.604575490392 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493276353174 : ℝ)) (s := (0.869872657002 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.606553519122 : ℝ) ≤ 0.682408233358 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606553519122 : ℝ)) (Q := (0.606553519122 : ℝ))
      (s := (0.795042658253 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777807444968 : ℝ)) (R := (0.778374076522 : ℝ)) (Q2 := (0.606553519122 : ℝ)) (T := (0.826548204381 : ℝ))
    (B := ((855556948764279/1250000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy40 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (123019577737/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6838808421141867/10000000000000000) := by
  have hk1 : kappa q ≤ 0.603779074761 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492078310948 : ℝ)) (s := (0.870550938139 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.605755618971 : ℝ) ≤ 0.681841774204 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605755618971 : ℝ)) (Q := (0.605755618971 : ℝ))
      (s := (0.795650758867 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.777295314418 : ℝ)) (R := (0.777861945972 : ℝ)) (Q2 := (0.605755618971 : ℝ)) (T := (0.826205079125 : ℝ))
    (B := ((6838808421141867/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy41 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (490880268721/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3416583758182443/5000000000000000) := by
  have hk1 : kappa q ≤ 0.602983198235 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490880268721 : ℝ)) (s := (0.871227043761 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604958258548 : ℝ) ≤ 0.681275967106 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604958258548 : ℝ)) (Q := (0.604958258548 : ℝ))
      (s := (0.796257185472 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776783193233 : ℝ)) (R := (0.777349824787 : ℝ)) (Q2 := (0.604958258548 : ℝ)) (T := (0.825862206529 : ℝ))
    (B := ((3416583758182443/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy42 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (97936445299/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6827532865936393/10000000000000000) := by
  have hk1 : kappa q ≤ 0.602187860240 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489682226495 : ℝ)) (s := (0.871900978928 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.604161437277 : ℝ) ≤ 0.680710810873 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604161437277 : ℝ)) (Q := (0.604161437277 : ℝ))
      (s := (0.796861943945 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.776271081063 : ℝ)) (R := (0.776837712617 : ℝ)) (Q2 := (0.604161437277 : ℝ)) (T := (0.825519586186 : ℝ))
    (B := ((6827532865936393/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy43 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (488484184269/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (106592257188223/156250000000000) := by
  have hk1 : kappa q ≤ 0.601393060201 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488484184269 : ℝ)) (s := (0.872572748669 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.603365154582 : ℝ) ≤ 0.680146304318 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603365154582 : ℝ)) (Q := (0.603365154582 : ℝ))
      (s := (0.797465040135 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775758977554 : ℝ)) (R := (0.776325609108 : ℝ)) (Q2 := (0.603365154582 : ℝ)) (T := (0.825177217691 : ℝ))
    (B := ((106592257188223/156250000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy44 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (243643071021/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (3408141144460487/5000000000000000) := by
  have hk1 : kappa q ≤ 0.600598797544 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487286142042 : ℝ)) (s := (0.873242357982 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.602569409890 : ℝ) ≤ 0.679582446256 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602569409890 : ℝ)) (Q := (0.602569409890 : ℝ))
      (s := (0.798066479853 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.775246882354 : ℝ)) (R := (0.775813513908 : ℝ)) (Q2 := (0.602569409890 : ℝ)) (T := (0.824835100637 : ℝ))
    (B := ((3408141144460487/5000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy45 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (60761012477/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6810666342823301/10000000000000000) := by
  have hk1 : kappa q ≤ 0.599805071706 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486088099816 : ℝ)) (s := (0.873909811833 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.601774202632 : ℝ) ≤ 0.679019235507 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601774202632 : ℝ)) (Q := (0.601774202632 : ℝ))
      (s := (0.798666268880 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774734795114 : ℝ)) (R := (0.775301426668 : ℝ)) (Q2 := (0.601774202632 : ℝ)) (T := (0.824493234622 : ℝ))
    (B := ((6810666342823301/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy46 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (48489005759/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (1701264153013049/2500000000000000) := by
  have hk1 : kappa q ≤ 0.599011882118 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484890057590 : ℝ)) (s := (0.874575115157 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600979532243 : ℝ) ≤ 0.678456670898 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600979532243 : ℝ)) (Q := (0.600979532243 : ℝ))
      (s := (0.799264412961 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.774222715485 : ℝ)) (R := (0.774789347039 : ℝ)) (Q2 := (0.600979532243 : ℝ)) (T := (0.824151619244 : ℝ))
    (B := ((1701264153013049/2500000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy47 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (120923003841/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6799453086942531/10000000000000000) := by
  have hk1 : kappa q ≤ 0.598219228221 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483692015364 : ℝ)) (s := (0.875238272857 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.600185398159 : ℝ) ≤ 0.677894751258 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600185398159 : ℝ)) (Q := (0.600185398159 : ℝ))
      (s := (0.799860917809 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773710643119 : ℝ)) (R := (0.774277274673 : ℝ)) (Q2 := (0.600185398159 : ℝ)) (T := (0.823810254106 : ℝ))
    (B := ((6799453086942531/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy48 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (482493973137/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (67938557578649/100000000000000) := by
  have hk1 : kappa q ≤ 0.597427109454 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482493973137 : ℝ)) (s := (0.875899289809 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.599391799822 : ℝ) ≤ 0.677333475420 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599391799822 : ℝ)) (Q := (0.599391799822 : ℝ))
      (s := (0.800455789102 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.773198577669 : ℝ)) (R := (0.773765209223 : ℝ)) (Q2 := (0.599391799822 : ℝ)) (T := (0.823469138808 : ℝ))
    (B := ((67938557578649/100000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy49 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (481295930911/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6788264615225411/10000000000000000) := by
  have hk1 : kappa q ≤ 0.596635525264 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481295930911 : ℝ)) (s := (0.876558170853 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.598598736674 : ℝ) ≤ 0.676772842223 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598598736674 : ℝ)) (Q := (0.598598736674 : ℝ))
      (s := (0.801049032490 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772686518789 : ℝ)) (R := (0.773253150343 : ℝ)) (Q2 := (0.598598736674 : ℝ)) (T := (0.823128272954 : ℝ))
    (B := ((6788264615225411/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy50 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (96019577737/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6782677408492059/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595844475098 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480097888685 : ℝ)) (s := (0.877214920804 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597806208164 : ℝ) ≤ 0.676212850511 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597806208164 : ℝ)) (Q := (0.597806208164 : ℝ))
      (s := (0.801640653586 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.772174466136 : ℝ)) (R := (0.772741097690 : ℝ)) (Q2 := (0.597806208164 : ℝ)) (T := (0.822787656153 : ℝ))
    (B := ((6782677408492059/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy51 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (239449923229/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (6777092302286829/10000000000000000) := by
  have hk1 : kappa q ≤ 0.595053958406 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478899846458 : ℝ)) (s := (0.877869544445 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.597014213740 : ℝ) ≤ 0.675653499129 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597014213740 : ℝ)) (Q := (0.597014213740 : ℝ))
      (s := (0.802230657974 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771662419365 : ℝ)) (R := (0.772229050919 : ℝ)) (Q2 := (0.597014213740 : ℝ)) (T := (0.822447288009 : ℝ))
    (B := ((6777092302286829/10000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem uniformEnergy52 {n : ℕ} (hn : 12227 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ (59712725529/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n) (finiteEnergy n n 0.011) q ≤ (677151336783717/1000000000000000) := by
  have hk1 : kappa q ≤ 0.594263974642 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477701804232 : ℝ)) (s := (0.878522046527 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.596222752856 : ℝ) ≤ 0.675094786929 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596222752856 : ℝ)) (Q := (0.596222752856 : ℝ))
      (s := (0.802819051205 : ℝ)) <;> norm_num
  have h := uniform_energy_upper_from_kappas hn (q := q)
    (U := (0.771150378135 : ℝ)) (R := (0.771717009689 : ℝ)) (Q2 := (0.596222752856 : ℝ)) (T := (0.822107168134 : ℝ))
    (B := ((677151336783717/1000000000000000) : ℝ)) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part264b
