import BstLean.Part291GroupedEBatch0
import BstLean.Part291GroupedEBatch1
import BstLean.Part291GroupedEBatch2
import BstLean.Part291SShared
import BstLean.Part291NormalizedO
import BstLean.Part263Events
import BstLean.Part291SplitE
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part246 BstLean.Part255 BstLean.Part264b
theorem lowUniformO {n : ℕ} (hn : 8000 ≤ n) :
    o3_kO n 46 ((mA n : ℝ)*(1/2+√23/n)) ((mA n : ℝ)*(1/2+√23/n)) ≤
      n * (42636997/1000000000) := by
  rw [norm_o (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowNormalizedO (lowInvDimension hn)) (by positivity)

theorem lowUniformS0W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (193409909 / 500000000) (367683783 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (193409909 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((367683783 / 500000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE0W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (193409909 / 500000000) (367683783 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (367683783 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (674021631 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowSplitE0W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum0W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (193409909 / 500000000) (367683783 / 500000000) (674021631 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS0W hn (c := (193409909 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS0W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE0W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS0C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (57745557 / 125000000) (125645833 / 200000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (57745557 / 125000000)).trans hc.1,
         hc.2.trans (by norm_num : ((125645833 / 200000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE0C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (57745557 / 125000000) (125645833 / 200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (125645833 / 200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (7587393 / 12500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowSplitE0C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum0C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (57745557 / 125000000) (125645833 / 200000000) (7587393 / 12500000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS0C hn (c := (57745557 / 125000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS0C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE0C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS1W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (193153297 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((734911287 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE1W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (734911287 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (673702321 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowSplitE1W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum1W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (193153297 / 500000000) (734911287 / 1000000000) (673702321 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS1W hn (c := (193153297 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS1W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE1W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS1C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (461458779 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((39233919 / 62500000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE1C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (39233919 / 62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (606717581 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowSplitE1C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum1C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (461458779 / 1000000000) (39233919 / 62500000) (606717581 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS1C hn (c := (461458779 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS1C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE1C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS2W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (385280557 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((734454819 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE2W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (734454819 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (673383227 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE2W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum2W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (385280557 / 1000000000) (734454819 / 1000000000) (673383227 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS2W hn (c := (385280557 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS2W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE2W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS2C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (230223829 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((627256151 / 1000000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE2C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (627256151 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (606443903 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE2C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum2C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (230223829 / 500000000) (627256151 / 1000000000) (606443903 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS2C hn (c := (230223829 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS2C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE2C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS4W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (96063767 / 250000000)).trans hc.1,
         hc.2.trans (by norm_num : ((733541317 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE4W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (733541317 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (672745683 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE4W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum4W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (96063767 / 250000000) (733541317 / 1000000000) (672745683 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS4W hn (c := (96063767 / 250000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS4W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE4W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS4C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (28714803 / 62500000)).trans hc.1,
         hc.2.trans (by norm_num : ((626282771 / 1000000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE4C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (626282771 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (302948543 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE4C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum4C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (28714803 / 62500000) (626282771 / 1000000000) (302948543 / 500000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS4C hn (c := (28714803 / 62500000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS4C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE4C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS6W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (191615063 / 500000000) (366313529 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (191615063 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((366313529 / 500000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE6W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (191615063 / 500000000) (366313529 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (366313529 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (336054497 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE6W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum6W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (191615063 / 500000000) (366313529 / 500000000) (336054497 / 500000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS6W hn (c := (191615063 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS6W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE6W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS6C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (458426349 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((156327257 / 250000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE6C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (156327257 / 250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (60535099 / 100000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE6C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum6C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (458426349 / 1000000000) (156327257 / 250000000) (60535099 / 100000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS6C hn (c := (458426349 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS6C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE6C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS8W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (38220573 / 100000000) (146342409 / 200000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (38220573 / 100000000)).trans hc.1,
         hc.2.trans (by norm_num : ((146342409 / 200000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE8W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (38220573 / 100000000) (146342409 / 200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (146342409 / 200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (335736579 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE8W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum8W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (38220573 / 100000000) (146342409 / 200000000) (335736579 / 500000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS8W hn (c := (38220573 / 100000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS8W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE8W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS8C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (457416159 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((15608373 / 25000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE8C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (15608373 / 25000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (604805611 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE8C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum8C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (457416159 / 1000000000) (15608373 / 25000000) (604805611 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS8C hn (c := (457416159 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS8C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE8C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS10W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (381181879 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((730796277 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE10W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (730796277 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (67083817 / 100000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE10W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum10W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (381181879 / 1000000000) (730796277 / 1000000000) (67083817 / 100000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS10W hn (c := (381181879 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS10W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE10W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS10C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (228203139 / 500000000) (9740007 / 15625000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (228203139 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((9740007 / 15625000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE10C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (228203139 / 500000000) (9740007 / 15625000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (9740007 / 15625000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (302130473 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE10C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum10C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (228203139 / 500000000) (9740007 / 15625000) (302130473 / 500000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS10C hn (c := (228203139 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS10C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE10C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS12W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (95039643 / 250000000)).trans hc.1,
         hc.2.trans (by norm_num : ((729879757 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE12W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (729879757 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (670204029 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE12W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum12W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (95039643 / 250000000) (729879757 / 1000000000) (670204029 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS12W hn (c := (95039643 / 250000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS12W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE12W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS12C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (455396707 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((622385613 / 1000000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE12C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (622385613 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (603716993 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE12C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum12C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (455396707 / 1000000000) (622385613 / 1000000000) (603716993 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS12C hn (c := (455396707 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS12C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE12C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS14W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (5923997 / 15625000)).trans hc.1,
         hc.2.trans (by norm_num : ((728962483 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE14W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (728962483 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (669570729 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE14W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum14W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (5923997 / 15625000) (728962483 / 1000000000) (669570729 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS14W hn (c := (5923997 / 15625000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS14W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE14W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS14C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (454387443 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((38838151 / 62500000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE14C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (38838151 / 62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (482539 / 800000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE14C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum14C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (454387443 / 1000000000) (38838151 / 62500000) (482539 / 800000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS14C hn (c := (454387443 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS14C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE14C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS16W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (189056793 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((728044459 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE16W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (728044459 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (668938269 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE16W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum16W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (189056793 / 500000000) (728044459 / 1000000000) (668938269 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS16W hn (c := (189056793 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS16W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE16W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS16C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (453378487 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((77554357 / 125000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE16C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (77554357 / 125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (301315607 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE16C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum16C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (453378487 / 1000000000) (77554357 / 125000000) (301315607 / 500000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS16C hn (c := (453378487 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS16C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE16C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS18W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (75418381 / 200000000)).trans hc.1,
         hc.2.trans (by norm_num : ((727125683 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE18W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (727125683 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (167076661 / 250000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE18W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum18W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (75418381 / 200000000) (727125683 / 1000000000) (167076661 / 250000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS18W hn (c := (75418381 / 200000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS18W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE18W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS18C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (452369839 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((309729467 / 500000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE18C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (309729467 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (602089383 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE18C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum18C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (452369839 / 1000000000) (309729467 / 500000000) (602089383 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS18C hn (c := (452369839 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS18C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE18C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS20W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (366904611 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((726206157 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE20W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (726206157 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (166918963 / 250000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE20W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum20W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (366904611 / 1000000000) (726206157 / 1000000000) (166918963 / 250000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS20W hn (c := (366904611 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS20W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE20W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS20C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (27643759 / 62500000) (12369653 / 20000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (27643759 / 62500000)).trans hc.1,
         hc.2.trans (by norm_num : ((12369653 / 20000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE20C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (27643759 / 62500000) (12369653 / 20000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (12369653 / 20000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (300774127 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE20C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum20C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (27643759 / 62500000) (12369653 / 20000000) (300774127 / 500000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS20C hn (c := (27643759 / 62500000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS20C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE20C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS40W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (178385151 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((716969799 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE40W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (716969799 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (330706501 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE40W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum40W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (178385151 / 500000000) (716969799 / 1000000000) (330706501 / 500000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS40W hn (c := (178385151 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS40W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE40W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS40C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (432260647 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((38043751 / 62500000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE40C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (38043751 / 62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (596175073 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE40C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum40C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (432260647 / 1000000000) (38043751 / 62500000) (596175073 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS40C hn (c := (432260647 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS40C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE40C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS60W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (69337607 / 200000000)).trans hc.1,
         hc.2.trans (by norm_num : ((707659223 / 1000000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE60W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (707659223 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (131045987 / 200000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE60W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum60W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (69337607 / 200000000) (707659223 / 1000000000) (131045987 / 200000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS60W hn (c := (69337607 / 200000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS60W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE60W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS60C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (26390681 / 62500000)).trans hc.1,
         hc.2.trans (by norm_num : ((598881659 / 1000000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE60C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (598881659 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (118173913 / 200000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE60C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum60C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (26390681 / 62500000) (598881659 / 1000000000) (118173913 / 200000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS60C hn (c := (26390681 / 62500000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS60C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE60C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS80W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (168328459 / 500000000) (69827511 / 100000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (168328459 / 500000000)).trans hc.1,
         hc.2.trans (by norm_num : ((69827511 / 100000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE80W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (168328459 / 500000000) (69827511 / 100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (69827511 / 100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (162280923 / 250000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE80W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum80W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (168328459 / 500000000) (69827511 / 100000000) (162280923 / 250000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS80W hn (c := (168328459 / 500000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS80W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE80W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS80C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (412270461 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((11780559 / 20000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE80C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (11780559 / 20000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (146407379 / 250000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE80C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum80C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (412270461 / 1000000000) (11780559 / 20000000) (146407379 / 250000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS80C hn (c := (412270461 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS80C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE80C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS100W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (326676107 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((344409047 / 500000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE100W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (344409047 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (20096609 / 31250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE100W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum100W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (326676107 / 1000000000) (344409047 / 500000000) (20096609 / 31250000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS100W hn (c := (326676107 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS100W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE100W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS100C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (20115947 / 50000000)).trans hc.1,
         hc.2.trans (by norm_num : ((579139237 / 1000000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE100C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (579139237 / 1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (290226413 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE100C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum100C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (20115947 / 50000000) (579139237 / 1000000000) (290226413 / 500000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS100C hn (c := (20115947 / 50000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS100C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE100C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS120W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (316744807 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((339644381 / 500000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE120W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (339644381 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (637130693 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE120W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum120W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (316744807 / 1000000000) (339644381 / 500000000) (637130693 / 1000000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS120W hn (c := (316744807 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS120W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE120W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS120C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (392395949 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((284607923 / 500000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE120C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (284607923 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (115067499 / 200000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE120C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum120C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (392395949 / 1000000000) (284607923 / 500000000) (115067499 / 200000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS120C hn (c := (392395949 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS120C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE120C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS140W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (30686227 / 100000000) (334843829 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.36 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSWide (lowInvDimension hn)
      (show B 0.3 0.74 c from
        ⟨(by norm_num : (0.3 : ℝ) ≤ (30686227 / 100000000)).trans hc.1,
         hc.2.trans (by norm_num : ((334843829 / 500000000) : ℝ) ≤ 0.74)⟩))

theorem lowUniformE140W {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (30686227 / 100000000) (334843829 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (334843829 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (315619411 / 500000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE140W (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum140W {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (30686227 / 100000000) (334843829 / 500000000) (315619411 / 500000000) (42636997/1000000000) 0.36
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS140W hn (c := (30686227 / 100000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS140W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE140W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem lowUniformS140C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * 0.2 :=
  lowS_from_normalized (by omega : 0 < n)
    (lowNormalizedSCore (lowInvDimension hn)
      (show B 0.38 0.63 c from
        ⟨(by norm_num : (0.38 : ℝ) ≤ (382501131 / 1000000000)).trans hc.1,
         hc.2.trans (by norm_num : ((279629041 / 500000000) : ℝ) ≤ 0.63)⟩))

theorem lowUniformE140C {n : ℕ} (hn : 8000 ≤ n) {c : ℝ}
    (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (279629041 / 500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (570281623 / 1000000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (lowGroupedE140C (lowInvDimension hn) hc) (by positivity)

theorem lowUniformNum140C {n : ℕ} (hn : 8000 ≤ n) :
    ta_num_sharp n (382501131 / 1000000000) (279629041 / 500000000) (570281623 / 1000000000) (42636997/1000000000) 0.2
      (BstLean.Part263.maskSlack n) 46 := by
  have ham := (lowUniformS140C hn (c := (382501131 / 1000000000)) ⟨le_rfl,by norm_num⟩).1
  refine ⟨lowUniformO hn,ham,?_⟩
  intro c hlo hhi
  have hs := lowUniformS140C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    lowUniformE140C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

end BstLean.BlueprintLow
